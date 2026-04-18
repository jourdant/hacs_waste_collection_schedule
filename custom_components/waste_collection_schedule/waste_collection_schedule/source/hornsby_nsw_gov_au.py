from __future__ import annotations

import datetime
import io
import json
import logging
import re
import urllib.parse
import urllib.request
from html.parser import HTMLParser
from statistics import median
from typing import Any, TypedDict

from waste_collection_schedule import Collection  # type: ignore[attr-defined]

TITLE = "Hornsby Shire Council"
DESCRIPTION = "Source for Hornsby Shire Council."
URL = "https://hornsby.nsw.gov.au/"
TEST_CASES = {
    "Residential test 1": {
        "address": "1 Cherrybrook Road, West Pennant Hills, 2125"
    },
    "Residential test 2": {
        "address": "10 Albion Street, Pennant Hills, 2120"
    },
    "Residential test 3": {
        "address": "20 Beecroft Road, Beecroft, 2119"
    }
}

HOW_TO_GET_ARGUMENTS_DESCRIPTION = {
    "en": "Use your full street address as shown in Hornsby's waste collection address search. Do not provide a geolocation ID; it is resolved automatically from your address."
}

PARAM_DESCRIPTIONS = {
    "en": {
        "address": (
            "Full street address exactly as shown on the Hornsby waste page, "
            "including suburb and postcode (without state/country)."
        )
    }
}

ICON_MAP = {
    "Green Waste": "mdi:leaf",
    "Recycling": "mdi:recycle",
    "General Waste": "mdi:trash-can",
    "Bulky Waste": "mdi:delete",
}

MONTH_NUM_MAP = {
    "JANUARY": 1,
    "FEBRUARY": 2,
    "MARCH": 3,
    "APRIL": 4,
    "MAY": 5,
    "JUNE": 6,
    "JULY": 7,
    "AUGUST": 8,
    "SEPTEMBER": 9,
    "OCTOBER": 10,
    "NOVEMBER": 11,
    "DECEMBER": 12,
}

BASE_URL = "https://www.hornsby.nsw.gov.au/"

WEEKLY_WASTE_TYPE_MAP = {"green": "Green Waste", "yellow": "Recycling"}
MIN_MARKER_SIZE = 10.0
MAX_MARKER_SIZE = 25.0
MONTH_YEAR_MAX_X_GAP = 30.0
SAME_LINE_TOP_TOLERANCE = 5.0
SHAPE_SIZE_TOLERANCE = 2.0
MIN_MARKERS_PER_COLOR = 10

_LOGGER = logging.getLogger(__name__)


RGB = tuple[float, float, float]
BBox = tuple[float, float, float, float]
DigitWord = tuple[int, BBox]


class PdfUrls(TypedDict):
    weekly: str | None
    bulky: str | None


class MonthHeader(TypedDict):
    month: str
    year: int
    bbox: BBox
    center: tuple[float, float]
    col: int | None


class MarkerShape(TypedDict):
    label: str
    x0: float
    top: float
    x1: float
    bottom: float


def _http_get(url: str, timeout_s: float = 25.0) -> bytes:
    """Perform an HTTP GET request and return the response body."""
    req = urllib.request.Request(
        url,
        headers={
            "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36",
            "Accept": "*/*",
            "Referer": "https://www.hornsby.nsw.gov.au/",
        },
        method="GET",
    )
    with urllib.request.urlopen(req, timeout=timeout_s) as resp:
        return resp.read()


def _parse_geolocation_id(response_bytes: bytes) -> str:
    """Parse the Hornsby address search response and return the best matching Id."""
    try:
        data = json.loads(response_bytes.decode("utf-8"))
    except (json.JSONDecodeError, UnicodeDecodeError) as e:
        raise ValueError(f"Address search response was not parseable: {e}") from e

    items = data.get("Items", [])
    if not items:
        raise ValueError("No address results returned.")

    best = max(items, key=lambda r: r.get("Score", 0))
    return best["Id"]


class _HrefExtractor(HTMLParser):
    """Simple HTML parser to extract href attributes from anchor tags."""

    def __init__(self) -> None:
        super().__init__()
        self.hrefs: list[str] = []

    def handle_starttag(self, tag: str, attrs: list[tuple[str, str | None]]) -> None:
        if tag.lower() != "a":
            return
        d = {k.lower(): v for k, v in attrs}
        href = d.get("href")
        if href:
            self.hrefs.append(href)


def _select_weekly_waste_calendar_pdf_href(hrefs: list[str]) -> str | None:
    """Select the weekly waste calendar PDF URL from the list of hrefs."""
    pdfs = [h for h in hrefs if h.lower().endswith(".pdf")]
    if not pdfs:
        return None

    # Strong signal: weekly waste calendar under 'suds-waste-and-recycling'
    cand = [
        h
        for h in pdfs
        if "collection-calendars" in h and "suds-waste-and-recycling" in h
    ]
    if cand:
        return cand[0]

    # Fallback: any collection-calendars PDF that doesn't look like bulky-waste
    cand = [
        h
        for h in pdfs
        if "collection-calendars" in h
        and "bulky" not in h.lower()
        and "suds-bulky-waste" not in h.lower()
    ]
    if cand:
        return cand[0]

    return pdfs[0]


def _select_bulky_waste_calendar_pdf_href(hrefs: list[str]) -> str | None:
    """Select the bulky waste calendar PDF URL from the list of hrefs."""
    pdfs = [h for h in hrefs if h.lower().endswith(".pdf")]
    if not pdfs:
        return None

    preferred = [
        h
        for h in pdfs
        if ("suds-bulky-waste" in h.lower())
        or ("bulkywasteflyer" in h.lower())
        or ("bulkywaste" in h.lower())
    ]
    if preferred:
        return preferred[0]

    cand = [h for h in pdfs if "bulky" in h.lower()]
    if cand:
        return cand[0]

    return None


def _resolve_pdf_urls_for_address(address: str, language: str = "en-AU") -> PdfUrls:
    """Resolve the PDF URLs for a given address via Hornsby Council API."""
    keywords = urllib.parse.quote(address, safe="")
    search_url = f"{BASE_URL}api/v1/myarea/search?keywords={keywords}"

    response_bytes = _http_get(search_url)
    geolocation_id = _parse_geolocation_id(response_bytes)

    waste_services_url = (
        f"{BASE_URL}ocapi/Public/myarea/wasteservices"
        f"?geolocationid={urllib.parse.quote(geolocation_id)}"
        f"&ocsvclang={urllib.parse.quote(language)}"
    )

    ws_json = json.loads(
        _http_get(waste_services_url).decode("utf-8", errors="replace")
    )
    if not ws_json.get("success", False):
        raise ValueError("wasteservices call returned success=false.")

    html = ws_json.get("responseContent") or ""
    if not html.strip():
        # No waste services content - address may not have collection services
        return {"weekly": None, "bulky": None}

    parser = _HrefExtractor()
    parser.feed(html)

    weekly_href = _select_weekly_waste_calendar_pdf_href(parser.hrefs)
    bulky_href = _select_bulky_waste_calendar_pdf_href(parser.hrefs)

    weekly_url = urllib.parse.urljoin(BASE_URL, weekly_href) if weekly_href else None
    bulky_url = urllib.parse.urljoin(BASE_URL, bulky_href) if bulky_href else None

    return {"weekly": weekly_url, "bulky": bulky_url}


def _is_near_white(rgb: RGB) -> bool:
    """Check if an RGB color is near white."""
    r, g, b = rgb
    return r > 0.95 and g > 0.95 and b > 0.95


def _classify_fill(rgb: RGB) -> str:
    """Classify fill color into 'green' or 'yellow'."""
    r, g, b = rgb
    if g > 0.45 and r < 0.45 and b < 0.45:
        return "green"
    if r > 0.70 and g > 0.55 and b < 0.45:
        return "yellow"
    return "unknown"


def _normalize_color_to_rgb(color: Any) -> RGB | None:
    """Normalize a pdfplumber color value to an RGB tuple (0-1 range)."""
    if color is None:
        return None
    if isinstance(color, (int, float)):
        v = float(color)
        return (v, v, v)
    if not isinstance(color, (tuple, list)):
        return None
    if len(color) == 1:
        v = float(color[0])
        return (v, v, v)
    if len(color) == 3:
        return (float(color[0]), float(color[1]), float(color[2]))
    if len(color) == 4:
        # CMYK to RGB conversion
        c, m, y, k = (float(x) for x in color)
        r = (1.0 - c) * (1.0 - k)
        g = (1.0 - m) * (1.0 - k)
        b = (1.0 - y) * (1.0 - k)
        return (r, g, b)
    return None


def _extract_month_headers(words: list[dict[str, Any]]) -> list[MonthHeader]:
    """Extract month headers from words by pairing month and year tokens."""
    month_name_set = set(MONTH_NUM_MAP.keys())
    headers: list[MonthHeader] = []

    for i, word in enumerate(words):
        month_text = word["text"].upper().strip()
        if month_text not in month_name_set:
            continue

        best_year_word = None
        best_gap = float("inf")
        for j, candidate_year in enumerate(words):
            if i == j:
                continue
            if abs(candidate_year["top"] - word["top"]) > SAME_LINE_TOP_TOLERANCE:
                continue
            if not re.fullmatch(r"\d{4}", candidate_year["text"].strip()):
                continue
            if candidate_year["x0"] < word["x1"]:
                continue
            gap = candidate_year["x0"] - word["x1"]
            if gap > MONTH_YEAR_MAX_X_GAP:
                continue
            if gap < best_gap:
                best_gap = gap
                best_year_word = candidate_year

        if best_year_word is None:
            continue

        x0 = min(word["x0"], best_year_word["x0"])
        x1 = max(word["x1"], best_year_word["x1"])
        top = min(word["top"], best_year_word["top"])
        bottom = max(word["bottom"], best_year_word["bottom"])

        headers.append(
            {
                "month": month_text,
                "year": int(best_year_word["text"].strip()),
                "bbox": (x0, top, x1, bottom),
                "center": ((x0 + x1) / 2.0, (top + bottom) / 2.0),
                "col": None,
            }
        )

    return headers


def _collect_colored_shapes(page: Any) -> list[MarkerShape]:
    """Collect colored marker-like shapes from page rects and curves."""
    shapes: list[MarkerShape] = []

    def _add_shape(label: str, x0: float, top: float, x1: float, bottom: float) -> None:
        if label == "unknown":
            return
        shapes.append(
            {
                "label": label,
                "x0": x0,
                "top": top,
                "x1": x1,
                "bottom": bottom,
            }
        )

    for rect in page.rects:
        if not rect.get("fill"):
            continue
        fill = _normalize_color_to_rgb(rect.get("non_stroking_color"))
        if fill is None or _is_near_white(fill):
            continue
        width = rect["x1"] - rect["x0"]
        height = rect["bottom"] - rect["top"]
        if not (MIN_MARKER_SIZE < width < MAX_MARKER_SIZE):
            continue
        if not (MIN_MARKER_SIZE < height < MAX_MARKER_SIZE):
            continue
        _add_shape(
            _classify_fill(fill),
            rect["x0"],
            rect["top"],
            rect["x1"],
            rect["bottom"],
        )

    for curve in page.curves:
        if not curve.get("fill"):
            continue
        fill = _normalize_color_to_rgb(curve.get("non_stroking_color"))
        if fill is None or _is_near_white(fill):
            continue
        width = curve["x1"] - curve["x0"]
        height = curve["bottom"] - curve["top"]
        if not (MIN_MARKER_SIZE < width < MAX_MARKER_SIZE):
            continue
        if not (MIN_MARKER_SIZE < height < MAX_MARKER_SIZE):
            continue
        _add_shape(
            _classify_fill(fill),
            curve["x0"],
            curve["top"],
            curve["x1"],
            curve["bottom"],
        )

    return shapes


def _build_marker_sets(
    colored_shapes: list[MarkerShape],
) -> dict[str, list[MarkerShape]]:
    """Group marker shapes by color and keep only consistent sizes."""
    by_label: dict[str, list[MarkerShape]] = {}
    for shape in colored_shapes:
        by_label.setdefault(shape["label"], []).append(shape)

    marker_sets: dict[str, list[MarkerShape]] = {}
    for label, items in by_label.items():
        widths = sorted(item["x1"] - item["x0"] for item in items)
        heights = sorted(item["bottom"] - item["top"] for item in items)
        med_w = median(widths)
        med_h = median(heights)

        keep = [
            item
            for item in items
            if abs((item["x1"] - item["x0"]) - med_w) < SHAPE_SIZE_TOLERANCE
            and abs((item["bottom"] - item["top"]) - med_h) < SHAPE_SIZE_TOLERANCE
        ]
        if len(keep) >= MIN_MARKERS_PER_COLOR:
            marker_sets[label] = keep

    return marker_sets


def _find_day_for_marker(
    marker: MarkerShape,
    digit_words: list[DigitWord],
) -> int | None:
    """Find day number for marker by containment then overlap area."""
    cx = (marker["x0"] + marker["x1"]) / 2.0
    cy = (marker["top"] + marker["bottom"]) / 2.0

    for digit, (wx0, wtop, wx1, wbottom) in digit_words:
        if wx0 <= cx <= wx1 and wtop <= cy <= wbottom:
            return digit

    best_day: int | None = None
    best_score = -1.0
    for digit, (wx0, wtop, wx1, wbottom) in digit_words:
        ix0 = max(marker["x0"], wx0)
        iy0 = max(marker["top"], wtop)
        ix1 = min(marker["x1"], wx1)
        iy1 = min(marker["bottom"], wbottom)
        if ix0 >= ix1 or iy0 >= iy1:
            continue
        score = (ix1 - ix0) * (iy1 - iy0)
        if score > best_score:
            best_score = score
            best_day = digit
    return best_day


def _extract_events_from_weekly_pdf(pdf_bytes: bytes) -> list[Collection]:
    """Extract green waste and recycling events from the weekly calendar PDF."""
    try:
        import pdfplumber
    except ImportError as e:
        raise ImportError(
            "pdfplumber is required for PDF extraction. "
            "Please install it with: pip install pdfplumber"
        ) from e

    with pdfplumber.open(io.BytesIO(pdf_bytes)) as doc:
        if len(doc.pages) < 1:
            raise ValueError("Empty PDF")

        page = doc.pages[0]

        # Use extract_words to get positioned text
        words = page.extract_words(x_tolerance=5, y_tolerance=3)
        headers = _extract_month_headers(words)

        if not headers:
            raise ValueError("No month headers found in PDF.")

        # Assign columns to headers using k-means-like clustering
        ncols = 4
        xs = [h["center"][0] for h in headers]
        xs_sorted = sorted(xs)
        n = len(xs_sorted)
        # Initial seeds at evenly-spaced quantiles
        centers = [
            xs_sorted[min(int(q * (n - 1) + 0.5), n - 1)]
            for q in (0.1 + i * 0.8 / (ncols - 1) for i in range(ncols))
        ]

        for _ in range(10):
            assignments = [
                min(range(ncols), key=lambda c: abs(x - centers[c])) for x in xs
            ]
            new_centers = list(centers)
            for c in range(ncols):
                members = [xs[i] for i in range(len(xs)) if assignments[i] == c]
                if members:
                    new_centers[c] = sum(members) / len(members)
            if all(abs(new_centers[c] - centers[c]) < 0.5 for c in range(ncols)):
                centers = new_centers
                break
            centers = new_centers

        col_centers = sorted(centers)

        for h in headers:
            h["col"] = min(
                range(len(col_centers)),
                key=lambda i: abs(h["center"][0] - col_centers[i]),
            )

        # Extract digit words with bounding boxes (top-down coordinates)
        digit_words: list[DigitWord] = []
        for w in words:
            if re.fullmatch(r"\d{1,2}", w["text"]):
                digit_words.append(
                    (int(w["text"]), (w["x0"], w["top"], w["x1"], w["bottom"]))
                )

        colored_shapes = _collect_colored_shapes(page)
        marker_sets = _build_marker_sets(colored_shapes)

        if not {"green", "yellow"}.issubset(marker_sets):
            raise ValueError(
                f"Could not detect both marker sets. Detected={list(marker_sets)}"
            )

        entries: list[Collection] = []
        seen: set[tuple[datetime.date, str]] = set()

        for color, markers in marker_sets.items():
            waste_type = WEEKLY_WASTE_TYPE_MAP.get(color)
            if waste_type is None:
                continue

            for marker in markers:
                cx = (marker["x0"] + marker["x1"]) / 2.0
                cy = (marker["top"] + marker["bottom"]) / 2.0

                day = _find_day_for_marker(marker, digit_words)
                if day is None:
                    continue

                # Find the month header for this marker
                col = min(
                    range(len(col_centers)),
                    key=lambda i: abs(cx - col_centers[i]),
                )
                candidates = [
                    h for h in headers if h["col"] == col and h["center"][1] <= cy + 1.0
                ]
                if candidates:
                    mh = max(candidates, key=lambda h: h["center"][1])
                else:
                    same_col = [h for h in headers if h["col"] == col]
                    mh = min(same_col, key=lambda h: abs(h["center"][1] - cy))

                month_num = MONTH_NUM_MAP[mh["month"]]
                try:
                    dt = datetime.date(mh["year"], month_num, day)
                except ValueError:
                    continue

                if (dt, waste_type) not in seen:
                    seen.add((dt, waste_type))
                    entries.append(
                        Collection(date=dt, t=waste_type, icon=ICON_MAP.get(waste_type))
                    )

                # General Waste is collected on both green and recycling weeks
                if (dt, "General Waste") not in seen:
                    seen.add((dt, "General Waste"))
                    entries.append(
                        Collection(
                            date=dt,
                            t="General Waste",
                            icon=ICON_MAP.get("General Waste"),
                        )
                    )

    return entries


def _extract_bulky_events_from_pdf(pdf_bytes: bytes) -> list[Collection]:
    """Extract bulky waste dates from the bulky waste flyer PDF."""
    try:
        import pdfplumber
    except ImportError as e:
        raise ImportError(
            "pdfplumber is required for PDF extraction. "
            "Please install it with: pip install pdfplumber"
        ) from e

    text_parts: list[str] = []
    with pdfplumber.open(io.BytesIO(pdf_bytes)) as doc:
        for page in doc.pages:
            try:
                page_text = page.extract_text()
                if page_text:
                    text_parts.append(page_text)
            except Exception:
                continue
    text = "\n".join(text_parts)

    date_pattern = re.compile(r"\b(\d{1,2})/(\d{1,2})/(\d{2,4})\b")
    seen: set[datetime.date] = set()
    entries: list[Collection] = []

    for m in date_pattern.finditer(text):
        day_s, month_s, year_s = m.groups()
        year = int(year_s)
        if year < 100:
            year += 2000
        try:
            dt = datetime.date(year, int(month_s), int(day_s))
        except ValueError:
            continue
        if dt in seen:
            continue
        seen.add(dt)
        entries.append(
            Collection(date=dt, t="Bulky Waste", icon=ICON_MAP.get("Bulky Waste"))
        )

    return entries


class Source:
    def __init__(self, address: str):
        self._address = address

    def fetch(self) -> list[Collection]:
        urls = _resolve_pdf_urls_for_address(self._address)
        entries: list[Collection] = []

        if urls["weekly"]:
            try:
                weekly_bytes = _http_get(urls["weekly"])
                entries.extend(_extract_events_from_weekly_pdf(weekly_bytes))
            except Exception as e:
                _LOGGER.warning("Failed to extract weekly calendar: %s", e)

        if urls["bulky"]:
            try:
                bulky_bytes = _http_get(urls["bulky"])
                entries.extend(_extract_bulky_events_from_pdf(bulky_bytes))
            except Exception as e:
                _LOGGER.warning("Failed to extract bulky waste calendar: %s", e)

        entries.sort(key=lambda e: e.date)
        return entries
