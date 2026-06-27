#!/usr/bin/env python3
"""
RadLit Digest — monthly radiology literature digest.

What it does, in order:
  1. Reads journals.yaml.
  2. For each journal, asks PubMed (free E-utilities API) for everything
     published in the trailing `lookback_days`.
  3. Pulls metadata (title, authors, abstract, DOI/link) for each article.
  4. For OPEN-ACCESS journals, also fetches full text + figures from PubMed Central.
  5. Summarizes each article with Gemini (full text if available, else abstract).
  6. Writes a single self-contained index.html dashboard.

It is deliberately conservative: it only ever reads from PubMed / PubMed Central,
which are free public APIs. It never logs into a publisher or scrapes paywalled text.
Subscription articles get an abstract-based summary plus a deep link you click to
read the full article through your own institutional login.
"""

import os
import sys
import time
import json
import html
import textwrap
import datetime as dt
import urllib.parse
import urllib.request
import urllib.error
import xml.etree.ElementTree as ET

import yaml

# ----------------------------------------------------------------------------
# Config / environment
# ----------------------------------------------------------------------------
EUTILS = "https://eutils.ncbi.nlm.nih.gov/entrez/eutils"
NCBI_KEY = os.environ.get("NCBI_API_KEY", "").strip()        # optional, raises rate limit
GEMINI_KEY = os.environ.get("GEMINI_API_KEY", "").strip()    # required for summaries
GEMINI_MODEL = os.environ.get("GEMINI_MODEL", "gemini-2.5-flash").strip()
CONTACT_EMAIL = os.environ.get("CONTACT_EMAIL", "radlit@example.com").strip()

HEADERS = {"User-Agent": f"RadLitDigest/1.0 (mailto:{CONTACT_EMAIL})"}
# Some publisher servers (e.g. IngentaConnect) reject non-browser User-Agents
# with HTTP 403. For those fetches we send a browser-like UA instead.
BROWSER_HEADERS = {
    "User-Agent": ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
                   "(KHTML, like Gecko) Chrome/120.0 Safari/537.36"),
    "Accept": "application/rss+xml, application/xml, text/xml, */*",
}


def http_get(url, retries=3, backoff=2.0, headers=None):
    hdrs = headers or HEADERS
    for attempt in range(retries):
        try:
            req = urllib.request.Request(url, headers=hdrs)
            with urllib.request.urlopen(req, timeout=60) as r:
                return r.read()
        except Exception as e:
            if attempt == retries - 1:
                raise
            time.sleep(backoff * (attempt + 1))


def eutils_url(endpoint, params):
    params = dict(params)
    if NCBI_KEY:
        params["api_key"] = NCBI_KEY
    return f"{EUTILS}/{endpoint}?{urllib.parse.urlencode(params)}"


# ----------------------------------------------------------------------------
# Step 1: find recent article PMIDs for a journal
# ----------------------------------------------------------------------------
def find_pmids(journal_ta, lookback_days, retmax):
    today = dt.date.today()
    start = today - dt.timedelta(days=lookback_days)
    term = (
        f'"{journal_ta}"[Journal] '
        f'AND ("{start:%Y/%m/%d}"[PDAT] : "{today:%Y/%m/%d}"[PDAT])'
    )
    url = eutils_url("esearch.fcgi", {
        "db": "pubmed", "term": term, "retmax": retmax, "retmode": "json",
    })
    data = json.loads(http_get(url))
    return data.get("esearchresult", {}).get("idlist", [])


# ----------------------------------------------------------------------------
# Step 2: fetch article metadata for a batch of PMIDs
# ----------------------------------------------------------------------------
def fetch_metadata(pmids):
    if not pmids:
        return []
    url = eutils_url("efetch.fcgi", {
        "db": "pubmed", "id": ",".join(pmids), "retmode": "xml",
    })
    root = ET.fromstring(http_get(url))
    articles = []
    for art in root.findall(".//PubmedArticle"):
        pmid = art.findtext(".//PMID", default="").strip()
        title = "".join(art.find(".//ArticleTitle").itertext()).strip() \
            if art.find(".//ArticleTitle") is not None else "(no title)"

        # Abstract (may have multiple labeled sections)
        abstract_parts = []
        for ab in art.findall(".//Abstract/AbstractText"):
            label = ab.get("Label")
            text = "".join(ab.itertext()).strip()
            abstract_parts.append(f"{label}: {text}" if label else text)
        abstract = "\n".join(abstract_parts).strip()

        # Authors
        authors = []
        for a in art.findall(".//Author"):
            last = a.findtext("LastName")
            init = a.findtext("Initials")
            if last:
                authors.append(f"{last} {init}" if init else last)
        author_str = ", ".join(authors[:6]) + (" et al." if len(authors) > 6 else "")

        # DOI / PMC id
        doi = pmc = ""
        for aid in art.findall(".//ArticleId"):
            idtype = aid.get("IdType")
            if idtype == "doi":
                doi = (aid.text or "").strip()
            elif idtype == "pmc":
                pmc = (aid.text or "").strip()

        pub = art.findtext(".//PubDate/Year") or art.findtext(".//PubDate/MedlineDate") or ""

        # Machine-readable date (YYYY-MM-DD) for client-side filtering.
        # Prefer the article's electronic/print pub date; fall back to entry date.
        iso_date = ""
        for path in [".//PubDate", ".//ArticleDate", ".//DateRevised", ".//DateCompleted"]:
            node = art.find(path)
            if node is not None:
                y = node.findtext("Year")
                m = node.findtext("Month") or "1"
                d = node.findtext("Day") or "1"
                if y:
                    months = {"jan":1,"feb":2,"mar":3,"apr":4,"may":5,"jun":6,
                              "jul":7,"aug":8,"sep":9,"oct":10,"nov":11,"dec":12}
                    mm = months.get(m[:3].lower(), m) if not str(m).isdigit() else m
                    try:
                        iso_date = f"{int(y):04d}-{int(mm):02d}-{int(d):02d}"
                        break
                    except (ValueError, TypeError):
                        continue
        if not iso_date:
            iso_date = f"{dt.date.today():%Y-%m-%d}"

        # Publication types from PubMed → a friendly category.
        ptypes = [ (pt.text or "").strip()
                   for pt in art.findall(".//PublicationType") if pt.text ]
        pl = [p.lower() for p in ptypes]
        def has(*keys): return any(k in p for p in pl for k in keys)
        if has("review"):
            art_type = "Review"
        elif has("case report"):
            art_type = "Case report"
        elif has("editorial", "comment", "letter"):
            art_type = "Editorial/Letter"
        elif has("clinical trial", "randomized", "observational", "comparative study",
                 "evaluation study", "multicenter"):
            art_type = "Primary research"
        elif has("journal article"):
            art_type = "Primary research"   # default for original articles
        else:
            art_type = "Other"

        link = f"https://doi.org/{doi}" if doi else f"https://pubmed.ncbi.nlm.nih.gov/{pmid}/"

        # MeSH headings (descriptor names) — used for neuro-filtering broad journals.
        mesh = [ (m.text or "").strip().lower()
                 for m in art.findall(".//MeshHeading/DescriptorName") if m.text ]

        articles.append({
            "pmid": pmid, "title": title, "abstract": abstract,
            "authors": author_str, "doi": doi, "pmc": pmc,
            "pubdate": pub, "iso_date": iso_date, "link": link,
            "art_type": art_type, "mesh": mesh, "fulltext": "",
        })
    return articles


# ----------------------------------------------------------------------------
# Alternative source: publisher RSS feed (for journals PubMed doesn't index)
# ----------------------------------------------------------------------------
def fetch_crossref_articles(issn, lookback_days, cap):
    """Fetch recent articles for a journal by ISSN from the free CrossRef API.
    CrossRef is built for automated querying, so it won't block us like a
    publisher site might. Returns articles in our standard shape."""
    start = (dt.date.today() - dt.timedelta(days=lookback_days)).isoformat()
    # Filter to items published since `start`, newest first.
    params = urllib.parse.urlencode({
        "filter": f"from-pub-date:{start}",
        "sort": "published",
        "order": "desc",
        "rows": min(cap, 200),
        "mailto": CONTACT_EMAIL,
    })
    url = f"https://api.crossref.org/journals/{issn}/works?{params}"
    try:
        data = json.loads(http_get(url))
    except Exception as e:
        print(f"  CrossRef fetch failed: {e}", file=sys.stderr)
        return []

    items = data.get("message", {}).get("items", [])
    articles = []
    for it in items:
        title = " ".join(it.get("title") or []) or "(untitled)"

        # Authors
        auths = []
        for a in it.get("author", []) or []:
            fam = a.get("family", "")
            giv = a.get("given", "")
            if fam:
                auths.append(f"{fam} {giv[:1]}." if giv else fam)
        authors = ", ".join(auths[:8]) + (" et al." if len(auths) > 8 else "")

        # Date: published-print / published-online / issued -> [Y, M, D]
        dparts = None
        for k in ("published-print", "published-online", "issued", "created"):
            if it.get(k, {}).get("date-parts"):
                dparts = it[k]["date-parts"][0]
                break
        if dparts:
            y = dparts[0]
            m = dparts[1] if len(dparts) > 1 else 1
            d = dparts[2] if len(dparts) > 2 else 1
            try:
                iso_date = dt.date(y, m, d).isoformat()
            except (ValueError, TypeError):
                iso_date = f"{dt.date.today():%Y-%m-%d}"
        else:
            iso_date = f"{dt.date.today():%Y-%m-%d}"

        # Abstract: CrossRef sometimes includes it as JATS-tagged text.
        abstract = re_strip_tags(it.get("abstract", "") or "")

        doi = it.get("DOI", "")
        link = f"https://doi.org/{doi}" if doi else (it.get("URL", "") or "")

        # Article type from CrossRef 'type' (journal-article, review-article, etc.)
        cr_type = (it.get("type", "") or "").replace("-", " ").title()

        articles.append({
            "pmid": "", "title": title, "abstract": abstract,
            "authors": authors, "doi": doi, "pmc": "",
            "pubdate": iso_date[:7], "iso_date": iso_date,
            "link": link, "art_type": cr_type or "Other", "mesh": [], "fulltext": "",
        })
    return articles


def fetch_rss_articles(rss_url, lookback_days, cap):
    """Parse a publisher RSS/Atom/RDF feed into our article shape.
    Handles RSS 2.0, Atom, and RSS 1.0 (RDF) with Dublin Core + PRISM
    extensions (as used by IngentaConnect). Returns a list of article dicts."""
    try:
        raw = http_get(rss_url, headers=BROWSER_HEADERS)
        root = ET.fromstring(raw)
    except Exception as e:
        print(f"  RSS fetch/parse failed: {e}", file=sys.stderr)
        return []

    # Strip namespaces so element lookups are prefix-independent.
    for el in root.iter():
        if "}" in el.tag:
            el.tag = el.tag.split("}", 1)[1]

    def text(node, *names):
        for n in names:
            f = node.find(n)
            if f is not None and (f.text or "").strip():
                return f.text.strip()
        return ""

    def all_text(node, name):
        return [ (e.text or "").strip() for e in node.findall(name) if (e.text or "").strip() ]

    # Channel-level cover date (PRISM) is the issue's date; used when items
    # lack their own date (common in Ingenta's per-issue feed).
    channel = root.find(".//channel")
    cover_date = ""
    if channel is not None:
        cover_date = text(channel, "coverDisplayDate", "date")
    issue_iso = parse_feed_date(cover_date) or f"{dt.date.today():%Y-%m-%d}"

    items = root.findall(".//item") or root.findall(".//entry")
    cutoff = dt.date.today() - dt.timedelta(days=lookback_days)
    articles = []

    for it in items[:cap]:
        title = text(it, "title") or "(untitled)"

        link = text(it, "link")
        if not link:
            la = it.find("link")
            if la is not None:
                link = la.get("href", "") or la.get("resource", "")
        if not link:
            # RDF items carry the URL in rdf:about (becomes 'about' attr after strip)
            link = it.get("about", "")

        # Abstract: feeds like Ingenta's don't include one; try common fields anyway.
        abstract = (text(it, "description", "summary", "abstract")
                    or text(it, "encoded"))
        abstract = re_strip_tags(abstract)

        # Authors: multiple <dc:creator> -> 'creator' after namespace strip.
        creators = all_text(it, "creator")
        if not creators:
            creators = all_text(it, "author")
        authors = ", ".join(creators[:8]) + (" et al." if len(creators) > 8 else "")

        # Date: per-item date if present, else the issue cover date.
        raw_date = text(it, "pubDate", "date", "published", "updated", "coverDisplayDate")
        iso_date = parse_feed_date(raw_date) or issue_iso

        try:
            if dt.date.fromisoformat(iso_date) < cutoff:
                continue
        except ValueError:
            pass

        # PRISM section (e.g. "Brain", "Head & Neck") makes a nice type-ish tag.
        section = text(it, "section")

        articles.append({
            "pmid": "", "title": title, "abstract": abstract,
            "authors": authors, "doi": "", "pmc": "",
            "pubdate": cover_date or iso_date[:7],
            "iso_date": iso_date,
            "link": link or rss_url,
            "art_type": section or "Other", "mesh": [], "fulltext": "",
        })
    return articles


def re_strip_tags(s):
    if not s:
        return ""
    import re, html as _html
    # Decode entities first (CrossRef/JATS abstracts are often entity-encoded),
    # then remove tags, then collapse whitespace.
    s = _html.unescape(s)
    s = re.sub(r"<[^>]+>", " ", s)
    s = re.sub(r"\s+", " ", s)
    return s.strip()


def parse_feed_date(s):
    """Return YYYY-MM-DD from common feed date formats, or '' if unparseable."""
    if not s:
        return ""
    s = s.strip()
    # ISO 8601 (Atom): 2026-05-01T...   -> take the date part
    if len(s) >= 10 and s[4] == "-" and s[7] == "-":
        return s[:10]
    # RFC 822 (RSS): 'Thu, 01 May 2026 00:00:00 GMT'
    import email.utils
    try:
        tup = email.utils.parsedate_tz(s)
        if tup:
            return dt.date(tup[0], tup[1], tup[2]).isoformat()
    except Exception:
        pass
    # PRISM coverDisplayDate: '1 October 2025' or 'October 2025'
    for fmt in ("%d %B %Y", "%B %Y", "%d %b %Y", "%b %Y"):
        try:
            return dt.datetime.strptime(s, fmt).date().isoformat()
        except ValueError:
            continue
    return ""


# ----------------------------------------------------------------------------
# Step 3: for open-access articles, pull full text + figures from PMC
# ----------------------------------------------------------------------------
def fetch_pmc_fulltext(pmc_id):
    """Returns (fulltext_string, [figure dicts]). pmc_id like 'PMC1234567'."""
    numeric = pmc_id.replace("PMC", "")
    url = eutils_url("efetch.fcgi", {
        "db": "pmc", "id": numeric, "retmode": "xml",
    })
    try:
        root = ET.fromstring(http_get(url))
    except Exception:
        return "", []

    # Body text
    paras = []
    for p in root.findall(".//body//p"):
        txt = "".join(p.itertext()).strip()
        if txt:
            paras.append(txt)
    fulltext = "\n\n".join(paras)

    # Figures: caption + image link on PMC
    figures = []
    for fig in root.findall(".//fig"):
        caption = "".join(fig.itertext()).strip()
        graphic = fig.find(".//graphic")
        href = ""
        if graphic is not None:
            # xlink:href namespace
            for k, v in graphic.attrib.items():
                if k.endswith("href"):
                    href = v
        # PMC serves figures under the article; build a viewable link
        if href:
            img_url = (
                f"https://www.ncbi.nlm.nih.gov/pmc/articles/{pmc_id}/bin/{href}.jpg"
            )
            figures.append({"caption": caption[:300], "url": img_url})
    return fulltext, figures


# ----------------------------------------------------------------------------
# Step 4: summarize with Gemini
# ----------------------------------------------------------------------------
def gemini_post(prompt, temperature=0.3, max_retries=3):
    """POST a prompt to Gemini, retrying briefly on 429 rate limits.
    Fails fast (short, bounded backoff) so a run can never stall for long."""
    url = (f"https://generativelanguage.googleapis.com/v1beta/models/"
           f"{GEMINI_MODEL}:generateContent?key={GEMINI_KEY}")
    payload = json.dumps({
        "contents": [{"parts": [{"text": prompt}]}],
        "generationConfig": {"temperature": temperature},
    }).encode()
    delay = 3.0
    for attempt in range(max_retries):
        req = urllib.request.Request(
            url, data=payload, headers={"Content-Type": "application/json"}, method="POST")
        try:
            with urllib.request.urlopen(req, timeout=60) as r:
                resp = json.loads(r.read())
            cand = (resp.get("candidates") or [{}])[0]
            parts = (cand.get("content") or {}).get("parts") or [{}]
            return parts[0].get("text", "")
        except urllib.error.HTTPError as e:
            if e.code == 429 and attempt < max_retries - 1:
                time.sleep(delay)
                delay += 3.0       # bounded: 3s, 6s — at most ~9s total, then give up
                continue
            raise
    return ""


def gemini_summarize(title, body, is_fulltext):
    if not GEMINI_KEY:
        return "(No GEMINI_API_KEY set — summary skipped. Add your key to enable summaries.)"

    source_note = "the FULL TEXT" if is_fulltext else "the ABSTRACT ONLY"
    prompt = textwrap.dedent(f"""
        You are summarizing a neuroradiology journal article for a practicing
        neuroradiologist doing monthly literature review. You are working from
        {source_note} of the article.

        Write a clear, useful summary. Adapt the structure to the article type:
        - For an educational/review/teaching article (e.g. a differential
          diagnosis or "lesions of the X" review), emphasize the key teaching
          points, the differential considerations, distinguishing imaging
          features, and the practical takeaway.
        - For original research, summarize the question, methods, key results,
          and clinical relevance.
        Keep medical terminology precise. Do not invent details not present in
        the source. If working from the abstract only, do not overstate.
        Aim for roughly 150-250 words. Use short paragraphs or bullet points,
        whichever fits the content.

        ARTICLE TITLE: {title}

        SOURCE TEXT:
        {body[:120000]}
    """).strip()

    try:
        txt = gemini_post(prompt, temperature=0.3)
        return txt.strip() if txt else "(Summary unavailable this run. The article link below still works.)"
    except Exception as e:
        return f"(Summary unavailable this run: {e}. The article link below still works.)"


# ----------------------------------------------------------------------------
# Step 5: build the HTML page
# ----------------------------------------------------------------------------
def render_html(sections, generated, videos=None, topics=None, build_log=None):
    videos = videos or []
    topics = topics or []
    build_log = build_log or []
    # Build a flat article list as JSON; the page filters it client-side.
    journals = []
    articles = []
    for sec in sections:
        journals.append({"name": sec["name"], "oa": sec["oa"]})
        for a in sec["articles"]:
            # Trim the full text we embed for the copy-prompt button so the page
            # doesn't balloon; ~6k chars is plenty for a detailed-summary request.
            ft = (a.get("fulltext") or "")[:6000]
            articles.append({
                "uid": "art_" + (a.get("pmid") or a["link"]),
                "journal": sec["name"], "oa": sec["oa"],
                "title": a["title"], "authors": a["authors"],
                "pubdate": a["pubdate"], "iso": a["iso_date"],
                "art_type": a.get("art_type", "Other"),
                "type_group": normalize_type(a.get("art_type", "Other")),
                "summary": a["summary"], "link": a["link"],
                "figures": a.get("figures", []),
                "abstract": a.get("abstract", ""), "fulltext": ft,
            })
    vid_list = []
    for v in videos:
        vid_list.append({
            "uid": "vid_" + v["vid"],
            "title": v["title"], "channel": v.get("channel", ""),
            "topic": v.get("topic", "Other"),
            "educational": v.get("educational", True),
            "iso": v["iso_date"], "thumb": v.get("thumb", ""),
            "link": v["link"],
            "description": (v.get("description", "") or "")[:400],
        })
    data_json = json.dumps({"articles": articles, "journals": journals,
                            "videos": vid_list, "topics": topics},
                           ensure_ascii=False)

    css = """
    :root{--bg:#0f1419;--card:#1a2129;--ink:#e6edf3;--muted:#9da7b3;
          --accent:#4da3ff;--line:#2a3540;--side:#141b22;}
    @media(prefers-color-scheme:light){:root{--bg:#f5f7fa;--card:#fff;
          --ink:#1a2129;--muted:#5a6573;--accent:#0969da;--line:#e1e6ec;--side:#eef1f5;}}
    *{box-sizing:border-box}
    body{margin:0;background:var(--bg);color:var(--ink);
         font:16px/1.6 -apple-system,BlinkMacSystemFont,"Segoe UI",Roboto,sans-serif}
    .layout{display:flex;min-height:100vh}
    .sidebar{width:240px;flex:0 0 240px;background:var(--side);
             border-right:1px solid var(--line);padding:20px 14px;
             position:sticky;top:0;height:100vh;overflow:auto}
    .sidebar h1{font-size:1.15rem;margin:0 0 2px}
    .sidebar .sub{color:var(--muted);font-size:.75rem;margin:0 0 18px}
    .jbtn{display:block;width:100%;text-align:left;background:none;border:none;
          color:var(--ink);font-size:.95rem;padding:9px 10px;border-radius:8px;
          cursor:pointer;margin-bottom:2px}
    .jbtn:hover{background:var(--line)}
    .jbtn.active{background:var(--accent);color:#fff;font-weight:600}
    .jbtn .ct{float:right;color:var(--muted);font-size:.8rem}
    .jbtn.active .ct{color:#fff}
    .main{flex:1;padding:24px 28px 80px;max-width:860px}
    .controls{display:flex;flex-wrap:wrap;gap:8px;margin-bottom:8px}
    .rbtn{background:var(--card);border:1px solid var(--line);color:var(--ink);
          padding:7px 13px;border-radius:20px;cursor:pointer;font-size:.85rem}
    .rbtn.active{background:var(--accent);color:#fff;border-color:var(--accent)}
    .custom{display:flex;gap:8px;align-items:center;margin:6px 0 18px;
            flex-wrap:wrap;font-size:.85rem;color:var(--muted)}
    .custom input{background:var(--card);border:1px solid var(--line);
                  color:var(--ink);padding:5px 8px;border-radius:6px}
    .count{color:var(--muted);font-size:.85rem;margin-bottom:14px}
    .badge{font-size:.7rem;font-weight:600;padding:2px 8px;border-radius:20px;margin-left:8px}
    .oa{background:#1f7a3f;color:#fff}.sub2{background:#7a5a1f;color:#fff}
    .tbadge{font-size:.7rem;font-weight:600;padding:2px 8px;border-radius:20px;
            margin-left:8px;background:#34507a;color:#fff}
    .card{background:var(--card);border:1px solid var(--line);border-radius:14px;
          padding:18px 20px;margin:14px 0}
    .card h3{margin:0 0 6px;font-size:1.05rem;line-height:1.35}
    .meta{color:var(--muted);font-size:.85rem;margin:0 0 12px}
    .summary{white-space:pre-wrap}
    .figs{display:flex;flex-wrap:wrap;gap:10px;margin-top:14px}
    .figs a img{height:90px;border-radius:8px;border:1px solid var(--line)}
    .actions{margin-top:14px;display:flex;gap:10px;flex-wrap:wrap}
    .btn{display:inline-block;background:var(--accent);color:#fff;text-decoration:none;
         padding:8px 16px;border-radius:8px;font-size:.9rem;font-weight:600;
         border:none;cursor:pointer}
    .btn.ghost{background:none;color:var(--accent);border:1px solid var(--accent)}
    .note{color:var(--muted);font-size:.8rem;margin-top:10px}
    .pager{display:flex;align-items:center;justify-content:center;gap:16px;
           margin:24px 0 8px}
    .pager .btn[disabled]{opacity:.35;pointer-events:none}
    .pageinfo{color:var(--muted);font-size:.85rem}
    .star{background:none;border:none;cursor:pointer;font-size:1.3rem;
          line-height:1;color:var(--muted);float:right;padding:0 0 0 10px}
    .star.on{color:#f5b301}
    .card h3{padding-right:4px}
    .modeswitch{display:flex;gap:6px;margin-bottom:16px}
    .selbtns{display:flex;gap:6px;margin:10px 0 6px}
    .selbtns button{flex:1;background:none;border:1px solid var(--line);color:var(--muted);
          font-size:.75rem;padding:5px;border-radius:6px;cursor:pointer}
    .selbtns button:hover{color:var(--ink);border-color:var(--accent)}
    .checkrow{display:flex;align-items:center;gap:9px;padding:8px 10px;border-radius:8px;
          cursor:pointer;font-size:.95rem}
    .checkrow:hover{background:var(--line)}
    .checkrow input{accent-color:var(--accent);width:16px;height:16px;cursor:pointer;flex:0 0 auto}
    .checkrow .nm{flex:1;min-width:0;overflow:hidden;text-overflow:ellipsis;white-space:nowrap}
    .checkrow .ct{color:var(--muted);font-size:.8rem}
    .jlabel{font-size:.72rem;font-weight:600;color:var(--accent);
          text-transform:uppercase;letter-spacing:.03em;margin:0 0 4px}
    .seclabel{font-size:.72rem;font-weight:700;color:var(--muted);
          text-transform:uppercase;letter-spacing:.04em;margin:18px 0 4px}
    .hidebtn{background:none;border:none;color:var(--muted);cursor:pointer;
          font-size:.8rem;padding:0;margin-left:14px;text-decoration:underline}
    .hidebtn:hover{color:var(--ink)}
    .modeswitch button{flex:1;background:var(--card);border:1px solid var(--line);
          color:var(--ink);padding:9px;border-radius:9px;cursor:pointer;font-weight:600}
    .modeswitch button.active{background:var(--accent);color:#fff;border-color:var(--accent)}
    .topichead{font-size:1.05rem;margin:26px 0 8px;padding-bottom:5px;
          border-bottom:2px solid var(--accent)}
    .vcard{display:flex;gap:14px;background:var(--card);border:1px solid var(--line);
          border-radius:14px;padding:14px;margin:12px 0}
    .vcard img{width:160px;height:90px;object-fit:cover;border-radius:8px;flex:0 0 160px}
    .vcard .vbody{flex:1;min-width:0}
    .vcard h4{margin:0 0 4px;font-size:1rem;line-height:1.35}
    .vcard .vmeta{color:var(--muted);font-size:.8rem;margin:0 0 8px}
    .vcard .vdesc{color:var(--muted);font-size:.85rem;
          display:-webkit-box;-webkit-line-clamp:2;-webkit-box-orient:vertical;overflow:hidden}
    @media(max-width:520px){.vcard{flex-direction:column}.vcard img{width:100%;flex:none;height:170px}}
    footer{color:var(--muted);font-size:.8rem;margin-top:50px}
    .menutoggle{display:none}
    @media(max-width:720px){
      .layout{flex-direction:column}
      .sidebar{position:static;width:auto;height:auto;flex:none}
      .main{padding:18px 16px 70px}
    }
    """
    js = """
    const DATA = __DATA__;
    let state = {mode:'articles', favView:false, hiddenView:false,
                 selJournals:null, selTopics:null, selTypes:null,
                 range:'365', from:null, to:null, page:0};
    const PAGE_SIZE = 10;
    const TYPE_BUCKETS = ['Review','Primary research','Case report','Editorial/Letter','Other'];

    // Initialize selection sets to "all checked" once DATA is known.
    function initSelections(){
      if(state.selJournals===null)
        state.selJournals = new Set(DATA.journals.map(j=>j.name));
      if(state.selTopics===null){
        const ts = new Set(DATA.videos.map(v=>v.topic));
        DATA.topics.forEach(t=>ts.add(t));
        state.selTopics = ts;
      }
      if(state.selTypes===null)
        state.selTypes = new Set(TYPE_BUCKETS);
    }

    function pageControls(totalItems){
      const pages = Math.ceil(totalItems / PAGE_SIZE);
      if(pages <= 1) return '';
      const cur = state.page + 1;
      const prevDis = state.page<=0 ? 'disabled' : '';
      const nextDis = state.page>=pages-1 ? 'disabled' : '';
      return '<div class="pager">'+
        '<button class="btn ghost" '+prevDis+' onclick="goPage('+(state.page-1)+')">&larr; Prev</button>'+
        '<span class="pageinfo">Page '+cur+' of '+pages+'</span>'+
        '<button class="btn ghost" '+nextDis+' onclick="goPage('+(state.page+1)+')">Next &rarr;</button>'+
        '</div>';
    }
    function goPage(p){ state.page=p; refresh(); window.scrollTo(0,0); }

    /* ----- Favorites storage -------------------------------------------------
       Swappable module. Today it uses the browser's localStorage (per-device,
       persists on the live GitHub Pages site). When we add cross-device sync,
       only Store.load / Store.save get swapped to call the cloud store — nothing
       else in the page changes. In this in-chat preview, localStorage may be
       unavailable, so it falls back to in-memory (stars work but reset on reload;
       on the real site they persist). */
    const Store = (function(){
      let mem = {};
      let hasLS = false;
      try { localStorage.setItem('__t','1'); localStorage.removeItem('__t'); hasLS = true; }
      catch(e){ hasLS = false; }
      return {
        load(key){
          if(hasLS){ try { return JSON.parse(localStorage.getItem(key)||'{}'); }
                     catch(e){ return {}; } }
          return mem[key]||{};
        },
        save(key,obj){
          if(hasLS){ try { localStorage.setItem(key, JSON.stringify(obj)); }
                     catch(e){} }
          else { mem[key]=obj; }
        }
      };
    })();

    let favs = Store.load('radlit_favs');   // { uid: {...} }
    function isFav(uid){ return !!favs[uid]; }
    function toggleFav(uid){
      const all = DATA.articles.concat(DATA.videos);
      const a = all.find(x=>x.uid===uid);
      if(!a) return;
      if(favs[uid]) delete favs[uid];
      else if(uid.indexOf('vid_')===0)
        favs[uid] = {title:a.title, link:a.link, topic:a.topic,
                     channel:a.channel, type:'video'};
      else
        favs[uid] = {title:a.title, link:a.link, journal:a.journal, type:'article'};
      Store.save('radlit_favs', favs);
      refresh();
    }

    let hidden = Store.load('radlit_hidden');   // { uid: {title, link, journal} }
    function isHidden(uid){ return !!hidden[uid]; }
    function toggleHidden(uid){
      const all = DATA.articles.concat(DATA.videos);
      const a = all.find(x=>x.uid===uid);
      if(!a) return;
      if(hidden[uid]) delete hidden[uid];
      else hidden[uid] = {title:a.title, link:a.link,
                          journal:a.journal||a.topic||''};
      Store.save('radlit_hidden', hidden);
      refresh();
    }

    function daysAgoISO(n){const d=new Date();d.setDate(d.getDate()-n);
      return d.toISOString().slice(0,10);}

    function inRange(iso){
      if(state.range==='custom'){
        if(state.from && iso < state.from) return false;
        if(state.to && iso > state.to) return false;
        return true;
      }
      return iso >= daysAgoISO(parseInt(state.range,10));
    }

    function filtered(){
      if(state.hiddenView){
        return DATA.articles.filter(a=>isHidden(a.uid))
          .sort((x,y)=> y.iso.localeCompare(x.iso));
      }
      if(state.favView){
        return DATA.articles.filter(a=>isFav(a.uid) && !isHidden(a.uid))
          .sort((x,y)=> y.iso.localeCompare(x.iso));
      }
      return DATA.articles.filter(a=>{
        if(isHidden(a.uid)) return false;
        if(!state.selJournals.has(a.journal)) return false;
        if(!state.selTypes.has(a.type_group||'Other')) return false;
        return inRange(a.iso);
      }).sort((x,y)=> y.iso.localeCompare(x.iso));
    }

    function esc(s){const d=document.createElement('div');d.textContent=s||'';
      return d.innerHTML;}

    function copyPrompt(i){
      const a = window.__cur[i];
      let body = a.fulltext && a.fulltext.length>50 ? a.fulltext
                 : (a.abstract || '');
      const label = a.fulltext && a.fulltext.length>50 ? 'full text' : 'abstract';
      const prompt =
        'Please give me a detailed summary of this neuroradiology article '+
        '('+label+' below). I am a neuroradiologist; emphasize teaching points, '+
        'differential diagnosis, distinguishing imaging features, and practical '+
        'takeaways.\\n\\nTITLE: '+a.title+'\\nLINK: '+a.link+'\\n\\n'+body;
      navigator.clipboard.writeText(prompt).then(()=>{
        const b=document.getElementById('cp'+i);
        b.textContent='Copied — paste into Claude';
        setTimeout(()=>{b.textContent='Summarize (copy for Claude)';},2500);
      });
    }

    function renderSidebar(){
      const counts={};
      DATA.articles.forEach(a=>{if(inRange(a.iso))counts[a.journal]=(counts[a.journal]||0)+1;});
      const favCount=Object.keys(favs).length;
      const hidCount=Object.keys(hidden).filter(k=>k.indexOf('art_')===0).length;
      let h='<button class="jbtn'+(state.favView?' active':'')+
            '" onclick="toggleFavView()">&#9733; Favorites<span class="ct">'+favCount+'</span></button>';
      h+='<button class="jbtn'+(state.hiddenView?' active':'')+
            '" onclick="toggleHiddenView()">&#128065; Hidden<span class="ct">'+hidCount+'</span></button>';
      // Journal checkboxes
      h+='<div class="seclabel">Journals</div>';
      h+='<div class="selbtns">'+
         '<button onclick="selectAllJournals(true)">Select all</button>'+
         '<button onclick="selectAllJournals(false)">Deselect all</button></div>';
      DATA.journals.forEach(j=>{
        const checked = state.selJournals.has(j.name) ? 'checked' : '';
        const jn = JSON.stringify(j.name).replace(/"/g,'&quot;');
        h+='<label class="checkrow"><input type="checkbox" '+checked+
           ' onchange="toggleJournal('+jn+')">'+
           '<span class="nm">'+esc(j.name.split(' (')[0])+'</span>'+
           '<span class="ct">'+(counts[j.name]||0)+'</span></label>';
      });
      // Type checkboxes
      const tcounts={};
      DATA.articles.forEach(a=>{if(inRange(a.iso)){const g=a.type_group||'Other';tcounts[g]=(tcounts[g]||0)+1;}});
      h+='<div class="seclabel">Article type</div>';
      h+='<div class="selbtns">'+
         '<button onclick="selectAllTypes(true)">All</button>'+
         '<button onclick="selectAllTypes(false)">None</button></div>';
      TYPE_BUCKETS.forEach(t=>{
        if(!tcounts[t]) return;
        const checked = state.selTypes.has(t) ? 'checked' : '';
        const tn = JSON.stringify(t).replace(/"/g,'&quot;');
        h+='<label class="checkrow"><input type="checkbox" '+checked+
           ' onchange="toggleType('+tn+')">'+
           '<span class="nm">'+esc(t)+'</span>'+
           '<span class="ct">'+tcounts[t]+'</span></label>';
      });
      document.getElementById('jlist').innerHTML=h;
    }

    function toggleJournal(name){
      if(state.selJournals.has(name)) state.selJournals.delete(name);
      else state.selJournals.add(name);
      state.favView=false; state.hiddenView=false; state.page=0; refresh();
    }
    function selectAllJournals(on){
      state.selJournals = on ? new Set(DATA.journals.map(j=>j.name)) : new Set();
      state.favView=false; state.hiddenView=false; state.page=0; refresh();
    }
    function toggleType(t){
      if(state.selTypes.has(t)) state.selTypes.delete(t);
      else state.selTypes.add(t);
      state.favView=false; state.hiddenView=false; state.page=0; refresh();
    }
    function selectAllTypes(on){
      state.selTypes = on ? new Set(TYPE_BUCKETS) : new Set();
      state.favView=false; state.hiddenView=false; state.page=0; refresh();
    }
    function toggleFavView(){ state.favView=!state.favView; state.hiddenView=false; state.page=0; refresh(); }
    function toggleHiddenView(){ state.hiddenView=!state.hiddenView; state.favView=false; state.page=0; refresh(); }

    function renderList(){
      const all=filtered();
      const special = state.favView || state.hiddenView;
      document.getElementById('controlsbar').style.display = special?'none':'flex';
      document.getElementById('customwrap').style.display =
        (!special && state.range==='custom')?'flex':'none';
      document.getElementById('count').textContent = state.hiddenView
        ? (all.length+' hidden item'+(all.length===1?'':'s'))
        : state.favView
        ? (all.length+' starred item'+(all.length===1?'':'s'))
        : (all.length+' article'+(all.length===1?'':'s')+' in range');
      const pages=Math.max(1,Math.ceil(all.length/PAGE_SIZE));
      if(state.page>pages-1) state.page=pages-1;
      const arts=all.slice(state.page*PAGE_SIZE,(state.page+1)*PAGE_SIZE);
      window.__cur=arts;
      let h='';
      if(!all.length) h='<p class="note">'+(state.hiddenView
        ? 'Nothing hidden. Use “Hide” on an article to remove it from the list.'
        : state.favView
        ? 'No favorites yet. Tap the &#9733; on any article to save it here.'
        : 'No articles to show. Tick a journal/type in the sidebar, or widen the date range.')+'</p>';
      arts.forEach((a,i)=>{
        const badge=a.oa?'<span class="badge oa">open access</span>'
                        :'<span class="badge sub2">subscription</span>';
        const tbadge = a.art_type ? '<span class="tbadge">'+esc(a.art_type)+'</span>' : '';
        const star='<button class="star'+(isFav(a.uid)?' on':'')+
                   '" title="Save to favorites" onclick="toggleFav('+
                   JSON.stringify(a.uid).replace(/"/g,'&quot;')+')">&#9733;</button>';
        let figs='';
        if(a.figures && a.figures.length){
          figs='<div class="figs">'+a.figures.slice(0,8).map(f=>
            '<a href="'+esc(f.url)+'" target="_blank" title="'+esc(f.caption)+'">'+
            '<img src="'+esc(f.url)+'" loading="lazy" alt="figure"></a>').join('')+'</div>';
        }
        const hasText = (a.abstract && a.abstract.length>20) ||
                        (a.fulltext && a.fulltext.length>50);
        const detailBtn = hasText ?
          '<button class="btn ghost" id="cp'+i+'" onclick="copyPrompt('+i+')">'+
          'Summarize (copy for Claude)</button>' : '';
        const accessNote = a.oa ? '' :
          '<p class="note">Subscription article — open it and sign in with your '+
          'institutional access (AJNR / ClinicalKey) for the full text.</p>';
        const bodyText = (a.abstract && a.abstract.length>20)
          ? a.abstract
          : a.summary;
        const hideBtn = '<button class="hidebtn" onclick="toggleHidden('+
          JSON.stringify(a.uid).replace(/"/g,'&quot;')+')">'+
          (state.hiddenView?'Unhide':'Hide')+'</button>';
        const jlabel = '<p class="jlabel">'+esc((a.journal||'').split(' (')[0])+'</p>';
        h+='<div class="card">'+jlabel+'<h3>'+star+esc(a.title)+badge+tbadge+'</h3>'+
           '<p class="meta">'+esc(a.authors)+' &middot; '+esc(a.pubdate)+'</p>'+
           '<div class="summary">'+esc(bodyText)+'</div>'+figs+
           '<div class="actions"><a class="btn" href="'+esc(a.link)+'" target="_blank">'+
           'Open full article &rarr;</a>'+detailBtn+hideBtn+'</div>'+accessNote+'</div>';
      });
      h += pageControls(all.length);
      document.getElementById('list').innerHTML=h;
    }

    /* ---- Video helpers ---- */
    function videoInRange(iso){ return inRange(iso); }

    function filteredVideos(){
      if(state.mode==='articles') return [];
      if(state.favView)
        return DATA.videos.filter(v=>isFav(v.uid)).sort((a,b)=>b.iso.localeCompare(a.iso));
      return DATA.videos
        .filter(v=>state.selTopics.has(v.topic) && videoInRange(v.iso))
        .sort((a,b)=>b.iso.localeCompare(a.iso));
    }

    function videoCard(v){
      const star='<button class="star'+(isFav(v.uid)?' on':'')+
                 '" title="Save to favorites" onclick="toggleFav('+
                 JSON.stringify(v.uid).replace(/"/g,'&quot;')+')">&#9733;</button>';
      const thumb = v.thumb ? '<img src="'+esc(v.thumb)+'" loading="lazy" alt="">' : '';
      return '<div class="vcard">'+thumb+'<div class="vbody"><h4>'+star+esc(v.title)+'</h4>'+
        '<p class="vmeta">'+esc(v.channel)+' &middot; '+esc(v.iso)+
        ' &middot; '+esc(v.topic)+'</p>'+
        '<p class="vdesc">'+esc(v.description)+'</p>'+
        '<div class="actions"><a class="btn" href="'+esc(v.link)+'" target="_blank">'+
        'Watch on YouTube &rarr;</a></div></div></div>';
    }

    function renderVideos(){
      const favView = state.favView;
      document.getElementById('controlsbar').style.display = favView?'none':'flex';
      document.getElementById('customwrap').style.display =
        (!favView && state.range==='custom')?'flex':'none';
      const vids=filteredVideos();
      document.getElementById('count').textContent = favView
        ? (vids.length+' starred video'+(vids.length===1?'':'s'))
        : (vids.length+' video'+(vids.length===1?'':'s')+' in range');
      let h='';
      if(!vids.length){
        h='<p class="note">'+(favView
          ? 'No starred videos yet. Tap the &#9733; on any video to save it.'
          : 'No videos to show. Tick a topic in the sidebar, or widen the date range.')+'</p>';
        document.getElementById('list').innerHTML=h; return;
      }
      if(favView){
        const pages=Math.max(1,Math.ceil(vids.length/PAGE_SIZE));
        if(state.page>pages-1) state.page=pages-1;
        const slice=vids.slice(state.page*PAGE_SIZE,(state.page+1)*PAGE_SIZE);
        h=slice.map(videoCard).join('')+pageControls(vids.length);
      } else {
        // group by topic; only checked topics are present in vids already
        const order = DATA.topics.slice();
        const groups={};
        vids.forEach(v=>{ (groups[v.topic]=groups[v.topic]||[]).push(v); });
        Object.keys(groups).forEach(t=>{ if(order.indexOf(t)<0) order.push(t); });
        order.forEach(t=>{
          if(!groups[t]) return;
          h+='<h3 class="topichead">'+esc(t)+' ('+groups[t].length+')</h3>';
          h+=groups[t].map(videoCard).join('');
        });
      }
      document.getElementById('list').innerHTML=h;
    }

    function renderSidebarVideos(){
      const favCount=Object.keys(favs).filter(k=>k.indexOf('vid_')===0).length;
      const counts={};
      DATA.videos.forEach(v=>{if(videoInRange(v.iso))counts[v.topic]=(counts[v.topic]||0)+1;});
      let h='<button class="jbtn'+(state.favView?' active':'')+
            '" onclick="toggleFavView()">&#9733; Favorites<span class="ct">'+
            favCount+'</span></button>';
      h+='<div class="selbtns">'+
         '<button onclick="selectAllTopics(true)">Select all</button>'+
         '<button onclick="selectAllTopics(false)">Deselect all</button></div>';
      const order=DATA.topics.slice();
      Object.keys(counts).forEach(t=>{if(order.indexOf(t)<0)order.push(t);});
      order.forEach(t=>{
        if(!counts[t]) return;
        const checked = state.selTopics.has(t) ? 'checked' : '';
        const tn = JSON.stringify(t).replace(/"/g,'&quot;');
        h+='<label class="checkrow"><input type="checkbox" '+checked+
           ' onchange="toggleTopic('+tn+')">'+
           '<span class="nm">'+esc(t)+'</span>'+
           '<span class="ct">'+counts[t]+'</span></label>';
      });
      document.getElementById('jlist').innerHTML=h;
    }

    function toggleTopic(t){
      if(state.selTopics.has(t)) state.selTopics.delete(t);
      else state.selTopics.add(t);
      state.favView=false; state.page=0; refresh();
    }
    function selectAllTopics(on){
      const all=new Set(DATA.videos.map(v=>v.topic));
      DATA.topics.forEach(t=>all.add(t));
      state.selTopics = on ? all : new Set();
      state.favView=false; state.page=0; refresh();
    }

    function refresh(){
      document.getElementById('mode_articles').classList.toggle('active', state.mode==='articles');
      document.getElementById('mode_videos').classList.toggle('active', state.mode==='videos');
      if(state.mode==='articles'){ renderSidebar(); renderList(); }
      else { renderSidebarVideos(); renderVideos(); }
    }
    function setMode(m){ state.mode=m; state.page=0; refresh(); }
    function setRange(r,el){
      state.range=r; state.page=0;
      document.querySelectorAll('.rbtn').forEach(b=>b.classList.remove('active'));
      if(el)el.classList.add('active');
      refresh();
    }
    function setCustom(){
      state.from=document.getElementById('dfrom').value||null;
      state.to=document.getElementById('dto').value||null;
      state.page=0;
      if(state.range==='custom') refresh();
    }
    window.addEventListener('DOMContentLoaded',()=>{
      initSelections();
      document.getElementById('dto').value=new Date().toISOString().slice(0,10);
      document.getElementById('dfrom').value=daysAgoISO(365);
      if(!DATA.videos || !DATA.videos.length)
        document.getElementById('mode_videos').style.display='none';
      refresh();
    });
    """

    range_buttons = [
        ("30", "Last month"), ("90", "Last 3 months"),
        ("180", "Last 6 months"), ("365", "Last year"), ("custom", "Custom range"),
    ]
    rbtns = "".join(
        f'<button class="rbtn{" active" if val=="365" else ""}" '
        f'onclick="setRange(\'{val}\',this)">{html.escape(lbl)}</button>'
        for val, lbl in range_buttons
    )

    build_log_html = html.escape("\n".join(build_log)) if build_log else "(none)"

    page = f"""<!doctype html><html><head><meta charset='utf-8'>
<meta name='viewport' content='width=device-width,initial-scale=1'>
<title>RadLit Digest</title><style>{css}</style></head><body>
<div class='layout'>
  <aside class='sidebar'>
    <h1>RadLit Digest</h1>
    <p class='sub'>Updated {html.escape(generated)}</p>
    <div class='modeswitch'>
      <button id='mode_articles' class='active' onclick="setMode('articles')">Articles</button>
      <button id='mode_videos' onclick="setMode('videos')">Videos</button>
    </div>
    <div id='jlist'></div>
  </aside>
  <main class='main'>
    <div class='controls' id='controlsbar'>{rbtns}</div>
    <div class='custom' id='customwrap' style='display:none'>
      <span>From</span><input type='date' id='dfrom' onchange='setCustom()'>
      <span>to</span><input type='date' id='dto' onchange='setCustom()'>
    </div>
    <p class='count' id='count'></p>
    <div id='list'></div>
    <footer>Sources: PubMed &amp; PubMed Central, and the YouTube Data API
    (open/free APIs). Summaries and topic labels are AI-generated and may contain
    errors — verify against the original before clinical use.
    <details style='margin-top:14px'><summary style='cursor:pointer'>Build diagnostics</summary>
    <pre style='white-space:pre-wrap;font-size:.75rem;opacity:.8'>{build_log_html}</pre>
    </details></footer>
  </main>
</div>
<script>{js.replace("__DATA__", data_json)}</script>
</body></html>"""
    return page


# ----------------------------------------------------------------------------
# YouTube: resolve channel, list recent uploads, classify by topic
# ----------------------------------------------------------------------------
YT_API = "https://www.googleapis.com/youtube/v3"
YT_KEY = os.environ.get("YOUTUBE_API_KEY", "").strip()


def yt_get(endpoint, params):
    params = dict(params)
    params["key"] = YT_KEY
    url = f"{YT_API}/{endpoint}?{urllib.parse.urlencode(params)}"
    return json.loads(http_get(url))


def yt_resolve_uploads_playlist(handle):
    """Resolve an @handle to the channel's 'uploads' playlist id."""
    # forHandle accepts the handle without the leading @
    h = handle.lstrip("@")
    data = yt_get("channels", {
        "part": "contentDetails,snippet", "forHandle": h,
    })
    items = data.get("items", [])
    if not items:
        # fallback: search for the channel
        s = yt_get("search", {"part": "snippet", "q": h, "type": "channel", "maxResults": 1})
        sit = s.get("items", [])
        if not sit:
            return None, None
        cid = sit[0]["snippet"]["channelId"]
        data = yt_get("channels", {"part": "contentDetails,snippet", "id": cid})
        items = data.get("items", [])
        if not items:
            return None, None
    up = items[0]["contentDetails"]["relatedPlaylists"]["uploads"]
    title = items[0]["snippet"]["title"]
    return up, title


def yt_list_videos(uploads_playlist, lookback_days, cap):
    """Return recent videos from the uploads playlist within lookback."""
    cutoff = (dt.date.today() - dt.timedelta(days=lookback_days)).isoformat()
    videos, token = [], None
    while len(videos) < cap:
        params = {"part": "snippet,contentDetails", "playlistId": uploads_playlist,
                  "maxResults": 50}
        if token:
            params["pageToken"] = token
        data = yt_get("playlistItems", params)
        for it in data.get("items", []):
            sn = it["snippet"]
            published = (it.get("contentDetails", {}).get("videoPublishedAt")
                         or sn.get("publishedAt", ""))[:10]
            if published and published < cutoff:
                return videos  # playlist is newest-first; we've passed the window
            vid = it["contentDetails"]["videoId"]
            thumbs = sn.get("thumbnails", {})
            thumb = (thumbs.get("medium") or thumbs.get("default") or {}).get("url", "")
            videos.append({
                "vid": vid,
                "title": sn.get("title", ""),
                "description": sn.get("description", "")[:1500],
                "iso_date": published or f"{dt.date.today():%Y-%m-%d}",
                "thumb": thumb,
                "link": f"https://www.youtube.com/watch?v={vid}",
                "channel": sn.get("channelTitle", ""),
            })
            if len(videos) >= cap:
                break
        token = data.get("nextPageToken")
        if not token:
            break
    return videos


def gemini_classify_video(title, description, topics):
    """Return (topic, is_educational). Falls back gracefully without a key."""
    if not GEMINI_KEY:
        return "Other", True
    topic_list = ", ".join(topics)
    prompt = textwrap.dedent(f"""
        You are organizing neuroradiology teaching videos. Given a video's title
        and description, do two things and reply with ONLY a JSON object, no
        markdown, no prose:
          1. "educational": true if this is teaching/educational content
             (lecture, case review, tutorial, didactic), false if it is a
             promo, announcement, vlog, trailer, or non-teaching clip.
          2. "topic": the single best-fitting topic from this list:
             [{topic_list}]. If it is educational but fits none well, you MAY
             return a short new topic name instead. If not educational, return "Other".

        Reply exactly like: {{"educational": true, "topic": "Spine"}}

        TITLE: {title}
        DESCRIPTION: {description[:1200]}
    """).strip()
    try:
        txt = gemini_post(prompt, temperature=0.0)
        if not txt:
            print(f"  [classify] empty response for '{title[:40]}'", file=sys.stderr)
            return "Other", True
        txt = txt.replace("```json", "").replace("```", "").strip()
        obj = json.loads(txt)
        topic = (obj.get("topic") or "Other").strip()
        edu = bool(obj.get("educational", True))
        return (topic if edu else "Other"), edu
    except Exception as e:
        print(f"  [classify] failed for '{title[:40]}': {e}", file=sys.stderr)
        return "Other", True


CACHE_FILE = "video_cache.json"


def load_video_cache():
    try:
        with open(CACHE_FILE) as f:
            return json.load(f)
    except (FileNotFoundError, ValueError):
        return {}


def save_video_cache(cache):
    try:
        with open(CACHE_FILE, "w") as f:
            json.dump(cache, f, indent=0)
    except Exception as e:
        print(f"  cache save failed: {e}", file=sys.stderr)


def gather_videos(vcfg, log=lambda m: None):
    lookback = vcfg.get("lookback_days", 366)
    cap = vcfg.get("max_videos_per_channel", 200)
    class_cap = vcfg.get("max_classifications_per_run", 80)
    topics = vcfg.get("topics", ["Other"])
    out = []
    classified = 0
    reused = 0
    topic_tally = {}
    cache = load_video_cache()   # { videoId: {"topic":..., "educational":bool} }
    if not YT_KEY:
        log("No YOUTUBE_API_KEY set — video section skipped.")
        return out, topics
    for ch in vcfg.get("channels", []):
        print(f"[YouTube: {ch.get('name', ch['handle'])}] resolving...", file=sys.stderr)
        uploads, title = yt_resolve_uploads_playlist(ch["handle"])
        if not uploads:
            log(f"YouTube: could not resolve channel @{ch['handle']} — check the handle.")
            continue
        vids = yt_list_videos(uploads, lookback, cap)
        log(f"YouTube @{ch['handle']}: {len(vids)} videos in window")
        for v in vids:
            vid = v["vid"]
            cached = cache.get(vid)
            if cached and cached.get("topic"):
                # Already classified in a previous run — reuse, no API call.
                topic, edu = cached["topic"], cached.get("educational", True)
                reused += 1
            elif classified < class_cap:
                topic, edu = gemini_classify_video(v["title"], v["description"], topics)
                classified += 1
                # Only cache successful (non-fallback) classifications, so a
                # quota-failed "Other" is retried next run rather than stuck.
                if topic != "Other" or edu is False:
                    cache[vid] = {"topic": topic, "educational": edu}
                time.sleep(15)   # free tier = 5 req/min; ~15s keeps us safely under
            else:
                topic, edu = "Other", True
            v["topic"] = topic
            v["educational"] = edu
            v["channel"] = v["channel"] or title
            topic_tally[topic] = topic_tally.get(topic, 0) + 1
            out.append(v)
    save_video_cache(cache)
    log(f"Video topics assigned: " +
        ", ".join(f"{k}={v}" for k, v in sorted(topic_tally.items())))
    log(f"Videos classified this run: {classified} new, {reused} reused from cache.")
    if classified and reused == 0 and topic_tally.get("Other", 0) == classified:
        log("WARNING: every newly classified video was 'Other' — the Gemini classify "
            "call is likely failing (rate limit / key). Cached topics are still used.")
    return out, topics


# ----------------------------------------------------------------------------
# Neuro filter — keep only neuroradiology articles from broad journals
# ----------------------------------------------------------------------------
NEURO_MESH = [
    "brain", "cerebr", "cerebell", "spinal cord", "spine", "vertebr",
    "nervous system", "neuro", "cranial", "skull", "meningeal", "meninges",
    "glioma", "glioblastoma", "astrocytoma", "medulloblastoma", "ependymoma",
    "intracranial", "subarachnoid", "head and neck", "temporal bone",
    "orbit", "optic", "facial", "trigeminal", "pituitary", "sella",
    "carotid", "stroke", "myelopathy", "demyelinating", "multiple sclerosis",
    "epilepsy", "hydrocephalus", "peripheral nerve",
]
NEURO_KEYWORDS = [
    "brain", "cerebral", "cerebellar", "cerebellum", "spine", "spinal",
    "vertebral", "cervical", "thoracic", "lumbar", "neuro", "neurologic",
    "intracranial", "cranial", "skull base", "head and neck", "temporal bone",
    "orbit", "orbital", "optic", "facial", "sinus", "sinonasal", "nasopharyn",
    "oropharyn", "larynx", "laryng", "thyroid", "parotid", "salivary",
    "glioma", "glioblastoma", "astrocytoma", "meningioma", "schwannoma",
    "medulloblastoma", "ependymoma", "pituitary", "sella", "carotid",
    "stroke", "infarct", "aneurysm", "hemorrhage", "demyelinat",
    "multiple sclerosis", "myelopathy", "epilepsy", "hydrocephalus",
    "white matter",
    # Specific neuro phrases kept; bare "nerve"/"plexus" removed because they
    # also match MSK/body articles. Legit neuro cases with these still pass via
    # their MeSH tags (NEURO_MESH) or the specific phrases below.
    "cranial nerve", "brachial plexus", "lumbosacral plexus", "nerve root",
    "optic nerve", "facial nerve", "trigeminal",
]


# ----------------------------------------------------------------------------
# IR filter — keep only interventional radiology articles from broad journals
# ----------------------------------------------------------------------------
IR_MESH = [
    "embolization", "embolism", "angioplasty", "stents", "stent",
    "catheter", "catheterization", "angiography", "chemoembolization",
    "radioembolization", "ablation", "thrombectomy", "thrombolysis",
    "biliary", "drainage", "nephrostomy", "hepatic artery", "portal vein",
    "transjugular intrahepatic portosystemic", "tips", "fistula",
    "vascular malformation", "arteriovenous malformation", "venous",
    "inferior vena cava", "ivc filter", "interventional radiology",
    "percutaneous", "fluoroscopy", "endovascular", "revascularization",
    "atherectomy", "fibroid", "uterine artery", "prostatic artery",
    "tumor ablation", "radiofrequency ablation", "microwave ablation",
    "cryoablation", "transarterial",
]
IR_KEYWORDS = [
    "embolization", "embolisation", "angioplasty", "stent", "stenting",
    "catheter", "catheterization", "catheterisation", "angiography",
    "chemoembolization", "chemoembolisation", "radioembolization",
    "transarterial", "ablation", "thrombectomy", "thrombolysis",
    "biliary drainage", "biliary stent", "cholangitis", "cholangioscopy",
    "nephrostomy", "ureteral stent", "hepatic artery", "portal hypertension",
    "portal vein", "transjugular", "tips", "tipss",
    "arteriovenous malformation", "avm", "vascular malformation",
    "inferior vena cava", "ivc filter", "venous access", "dialysis access",
    "interventional radiology", "interventional oncology",
    "percutaneous", "endovascular", "revascularization",
    "uterine artery embolization", "uterine fibroid embolization",
    "prostatic artery embolization", "prostate artery embolization",
    "radiofrequency ablation", "microwave ablation", "cryoablation",
    "tumor ablation", "hepatic ablation", "renal ablation",
    "y90", "y-90", "yttrium", "sir-spheres", "therasphere",
    "varicocele", "pelvic congestion", "lymphangiography",
    "thoracic duct", "lymphatic intervention",
]


def is_ir_article(a):
    """True if an article looks like interventional radiology content
    (MeSH terms first, then a title/abstract keyword backstop)."""
    for m in a.get("mesh", []):
        for term in IR_MESH:
            if term in m:
                return True
    hay = (a.get("title", "") + " " + a.get("abstract", "")).lower()
    for kw in IR_KEYWORDS:
        if kw in hay:
            return True
    return False


def normalize_type(t):
    """Fold PubMed and CrossRef type labels into canonical filter buckets."""
    s = (t or "").lower()
    if "review" in s:
        return "Review"
    if "case" in s:
        return "Case report"
    if "editorial" in s or "letter" in s or "comment" in s:
        return "Editorial/Letter"
    if "research" in s or "journal article" in s or "article" in s:
        return "Primary research"
    return "Other"


def is_neuro_article(a):
    """True if an article looks like neuroradiology content (MeSH first, then
    a title/abstract keyword backstop)."""
    for m in a.get("mesh", []):
        for term in NEURO_MESH:
            if term in m:
                return True
    hay = (a.get("title", "") + " " + a.get("abstract", "")).lower()
    for kw in NEURO_KEYWORDS:
        if kw in hay:
            return True
    return False


# ----------------------------------------------------------------------------
# Main
# ----------------------------------------------------------------------------
def main():
    BUILD_LOG = []
    def log(msg):
        print(msg, file=sys.stderr)
        BUILD_LOG.append(msg)

    with open("journals.yaml") as f:
        cfg = yaml.safe_load(f)

    lookback = cfg.get("lookback_days", 366)
    cap = cfg.get("max_articles_per_journal", 400)
    ezproxy = (cfg.get("ezproxy_prefix") or "").strip()
    sections = []

    for j in cfg["journals"]:
        print(f"[{j['name']}] searching...", file=sys.stderr)
        if j.get("source") == "rss" and j.get("rss_url"):
            meta = fetch_rss_articles(j["rss_url"], lookback, cap)
            log(f"{j['name']}: {len(meta)} articles found via RSS feed")
        elif j.get("source") == "crossref" and j.get("issn"):
            meta = fetch_crossref_articles(j["issn"], lookback, cap)
            log(f"{j['name']}: {len(meta)} articles found via CrossRef")
        else:
            pmids = find_pmids(j["pubmed_ta"], lookback, cap)
            log(f"{j['name']}: {len(pmids)} articles found in PubMed")
            # efetch handles batches; chunk to be safe with large years
            meta = []
            for i in range(0, len(pmids), 100):
                meta.extend(fetch_metadata(pmids[i:i+100]))
                time.sleep(0.4)

        # Optional subject filter for broad/general journals.
        if j.get("filter") == "neuro":
            before = len(meta)
            meta = [a for a in meta if is_neuro_article(a)]
            log(f"{j['name']}: neuro filter kept {len(meta)} of {before} articles")
        elif j.get("filter") == "ir":
            before = len(meta)
            meta = [a for a in meta if is_ir_article(a)]
            log(f"{j['name']}: IR filter kept {len(meta)} of {before} articles")

        out_articles = []
        for a in meta:
            figs, is_full = [], False
            if j["open_access"] and a["pmc"]:
                ft, figures = fetch_pmc_fulltext(a["pmc"])
                if ft:
                    figs, is_full = figures, True
                    a["fulltext"] = ft   # kept for the on-demand detailed-summary prompt

            has_text = bool((a["abstract"] or "").strip()) or is_full
            # No automatic LLM summaries — keeps runs fast and inside the free tier.
            # Each article gets a "Summarize" button (copy-prompt to Claude) instead.
            if has_text:
                a["summary"] = ("Tap \u201cSummarize\u201d to generate a summary on demand. "
                                "The abstract is shown below; the button copies it "
                                "(or the full text, when available) into a prompt for Claude.")
            else:
                a["summary"] = ("No abstract is available from this source. "
                                "Open the article to read it in full.")
            a["figures"] = figs
            # Route links through EZproxy only for journals flagged ezproxy: true
            # (the ones accessed via ClinicalKey). All others keep direct links.
            if ezproxy and j.get("ezproxy") and a.get("link"):
                a["link"] = ezproxy + a["link"]
            out_articles.append(a)

        sections.append({
            "name": j["name"], "oa": j["open_access"], "articles": out_articles,
        })

    # Videos (optional — only runs if videos.yaml exists and a YT key is set)
    videos, topics = [], []
    try:
        with open("videos.yaml") as f:
            vcfg = yaml.safe_load(f)
        videos, topics = gather_videos(vcfg, log)
    except FileNotFoundError:
        log("No videos.yaml — video section skipped.")

    generated = dt.datetime.now().strftime("%B %d, %Y")
    html_out = render_html(sections, generated, videos, topics, BUILD_LOG)
    with open("index.html", "w") as f:
        f.write(html_out)
    print("Wrote index.html", file=sys.stderr)


if __name__ == "__main__":
    main()
