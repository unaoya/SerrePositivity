"""Write the citation CSV for a checkout of SerrePositivity.

Usage: python3 extract_citations.py REPO > citations.csv
"""
import csv
from pathlib import Path
import re
import subprocess
import sys

# Long names precede their component surnames. ASCII boundaries keep Japanese
# particles adjacent to a citation while excluding pieces of Lean identifiers.
DASH = r"[-‐‑–—−]"
ALIASES = {
    "論文": r"本論文|元論文|原論文|論文|Positivity of Serre['’]s Intersection Multiplicity",
    "KST": rf"KST(?:18)?|Kerz(?:\s*{DASH}\s*|,\s*|\s+)Strunk(?:\s*{DASH}\s*|,\s*(?:and )?|\s+)Tamme|1611\.08466(?:v\d+)?|Algebraic K.theory and descent for blow.ups",
    "Land–Tamme": rf"Land(?:\s*{DASH}\s*|\s+and\s+|\s*&\s*|\s+)Tamme|LT(?:19)?|1808\.05559(?:v\d+)?|On the K.theory of pullbacks",
    "Tamme": r"(?:Georg )?Tamme|Tam18|1703\.03331(?:v\d+)?|Excision in algebraic K.theory revisited",
    "BGT": rf"BGT(?:13)?|Blumberg(?:\s*{DASH}\s*|,\s*|\s+)Gepner(?:\s*{DASH}\s*|,\s*(?:and )?|\s+)Tabuada|1001\.2282(?:v\d+)?|A universal characterization of higher algebraic K.theory",
    "Waldhausen": r"Waldhausen|Wal85",
    "Barwick": r"Barwick",
    "Thomason–Trobaugh": rf"Thomason\s*{DASH}\s*Trobaugh|TT90|TT(?=\s+(?:§|[0-9]))",
    "Thomason": r"Thomason",
    "Neeman": r"Neeman",
    "9 人論文": r"9\s*人論文|九人論文|[Aa]ntieau et al\.",
    "Drinfeld": r"Drinfeld|Dri04",
    "Kuznetsov–Lunts": rf"Kuznetsov\s*{DASH}\s*Lunts",
    "Schlichting": r"Schlichting",
    "Balmer–Schlichting": rf"Balmer\s*{DASH}\s*Schlichting",
    "Goodwillie": r"Goodwillie|Goo86",
    "Stacks": r"Stacks(?: Project)?",
}
REFERENCES = list(ALIASES)
PRIMARY = set(REFERENCES[:5])
ORDER = sorted(REFERENCES, key=lambda ref: -len(ref))
SOURCE = re.compile(
    r"(?<![A-Za-z0-9_])(?:"
    + "|".join(f"(?P<r{REFERENCES.index(ref)}>{ALIASES[ref]})" for ref in ORDER)
    + r")(?![A-Za-z0-9_])",
    re.I,
)
TOKEN = re.compile(r'/\*|/-|--[^\n]*|"(?:[^"\\]|\\.)*"', re.S)
COMMENT = re.compile(r"/-|-/")
KIND = (
    r"Theorem|Thm|Lemma|Lemme|Lem|Proposition|Prop|Corollary|Cor|"
    r"Definition|Def|Remark|Rem|Example|Ex|Construction|Constr|Claims?|"
    r"Recollection|Notation|Observation|定理|補題|命題|系|定義|注意|例|構成|式|図式"
)
NUM = r"[A-Z]\.\d+(?:\.\d+)*|\d+(?:\.\d+)*[a-c]?|[A-Z]"
TYPED = re.compile(
    rf"(?:(?P<kind>{KIND})\.?[\s*`]*|(?P<section>§+|(?:Sec(?:tion)?|App(?:endix)?)\.?\s*)\s*)"
    rf"(?P<num>{NUM})(?![A-Za-z0-9_]|\.\d)", re.I
)
DISPLAY = re.compile(r"(?:式\s*|図式\s*)?\(\s*(?P<num>\d+(?:\.\d+)*|[A-Z]\.\d+)\s*\)", re.I)
BARE = re.compile(rf"(?P<num>{NUM})(?![A-Za-z0-9_]|\.\d)", re.I)
INTRO = re.compile(r"[\s*\x60\[\],，:：の]*")
CHAIN = re.compile(
    rf"(?:[\s*`]+|[\s*`]*(?:(?:と|および|及び|and|&|・|、|,|，)|{DASH}|〜)[\s*`]*)"
)
REVERSE = re.compile(r"[\s*\x60()（）\[\],，:：]*$")
PAPER_PATH = re.compile(r"^SerrePositivity/(?:Paper/|Inputs/Descent\.lean$|KST/Descent/)")
STACKS = re.compile(r"(?:(?:Tag)\.?\s*)?0815\b", re.I)


def docstrings(source):
    """Yield the text and offset of each top-level module or declaration doc."""
    offset = 0
    while token := TOKEN.search(source, offset):
        offset = token.end()
        if token[0] != "/-":
            continue
        doc = source[offset:offset + 1] in ("!", "-")
        start = offset + 1
        depth = 1
        for delimiter in COMMENT.finditer(source, offset):
            depth += 1 if delimiter[0] == "/-" else -1
            if depth == 0:
                offset = delimiter.end()
                if doc:
                    # Blank nested comments, retaining offsets and line breaks.
                    body = source[start:delimiter.start()]
                    nested = 0
                    cursor = 0
                    parts = []
                    for mark in COMMENT.finditer(body):
                        if nested == 0 and mark[0] == "/-":
                            parts.append(body[cursor:mark.start()])
                            cursor = mark.start()
                        nested += 1 if mark[0] == "/-" else -1
                        if nested == 0:
                            parts.append(re.sub(r"[^\n]", " ", body[cursor:mark.end()]))
                            cursor = mark.end()
                    parts.append(body[cursor:])
                    yield start, "".join(parts)
                break
        else:
            raise ValueError(f"Unterminated block comment at offset {token.start()}")


def normalize(match, prior=""):
    number = match["num"]
    if not number[0].isdigit():
        number = number.upper()
    if match.re is DISPLAY:
        return f"({number})"
    if match.re is TYPED:
        if match["section"]:
            return f"§{number}"
        if match["kind"] in ("式", "図式"):
            return f"({number})"
        return number
    if prior.startswith("§"):
        return f"§{number}"
    if prior.startswith("("):
        return f"({number})"
    return number


def match_number(body, start, allow_bare, ref):
    if ref == "Stacks":
        return STACKS.match(body, start)
    if ref == "Goodwillie":
        return re.compile(r"(?:[Mm]ain [Tt]heorem|主定理)").match(body, start)
    if ref == "論文":
        qualifier = re.compile(r"(?:(?:一般係数版|一般係数つき|原典の)\s*)*")
        start = qualifier.match(body, start).end()
    return (
        TYPED.match(body, start)
        or DISPLAY.match(body, start)
        or (BARE.match(body, start) if allow_bare else None)
    )


def source_name(match):
    return REFERENCES[int(match.lastgroup[1:])]


def explicit(body):
    mentions = list(SOURCE.finditer(body))
    for index, mention in enumerate(mentions):
        ref = source_name(mention)
        gap = INTRO.match(body, mention.end())
        start = gap.end()
        edition = re.match(r"(?:v\d+|(?:19|20)\d\d|LNM 1126)[)）.,\s]+", body[start:], re.I)
        if edition:
            start += edition.end()
        follow = body[start:]
        allow_bare = ref != "論文" and (
            follow.startswith(("§", "("))
            or re.match(r"(?:[A-Z]\.\d+|\d+\.\d+|[A-Z]\s*\]|\d+\s*\])", follow)
        )
        if ref == "Tamme" and index and source_name(mentions[index - 1]) == "Land–Tamme":
            if re.fullmatch(r"\s*[/&・]\s*", body[mentions[index - 1].end():mention.start()]):
                continue
        if ref == "論文" and mention[0] == "原論文" and re.search(
            r"[A-Za-z]\s+$", body[max(0, mention.start() - 30):mention.start()]
        ):
            continue
        if ref == "KST" and (
            re.match(r"(?:D|T|L)\d+\b", follow) or body[mention.end():].startswith(("/", "."))
        ):
            continue
        if ref == "KST" and follow.startswith("§10-7"):
            yield start, ref, "§10-7"
            continue
        if ref == "論文" and not (
            body[mention.end():].startswith(("の", " ", "（", ":")) or follow.startswith(("§", "("))
        ):
            # Direct forms such as 論文補題4.6 still count.
            if not TYPED.match(body, start):
                continue
        if ref == "Land–Tamme" and mention[0].upper() in ("LT", "LT19") and not (
            TYPED.match(body, start) or allow_bare
        ):
            continue
        bound = mentions[index + 1].start() if index + 1 < len(mentions) else len(body)
        first = match_number(body, start, allow_bare, ref)
        if first and first.start() < bound:
            prior = ""
            while first and first.start() < bound:
                if ref in ("Stacks", "Goodwillie"):
                    number = "0815" if ref == "Stacks" else "Main Theorem"
                else:
                    number = normalize(first, prior)
                yield first.start(), ref, number
                prior = number
                separator = CHAIN.match(body, first.end())
                if not separator or ref in ("Stacks", "Goodwillie"):
                    break
                # Commas commonly start citations of other works. Bare list
                # numbers must look like this reference's previous number.
                after = separator.end()
                first = match_number(body, after, True, ref)
                if first and first.re is BARE:
                    bare = first["num"]
                    if not any(c.isdigit() for c in bare) or ("." in prior and "." not in bare):
                        break
                    if not separator[0].strip() or re.match(r"[pP]\.\d", first[0]):
                        break
        else:
            before = body[max(0, mention.start() - 45):mention.start()]
            reverse = next(
                (m for m in reversed(list(TYPED.finditer(before))) if REVERSE.fullmatch(before[m.end():])),
                None,
            )
            if reverse and ref != "論文" and re.match(r"\s*[)）\]]", body[mention.end():]):
                at = max(0, mention.start() - 45) + reverse.start()
                yield at, ref, normalize(reverse)
            elif ref in PRIMARY and (
                ref != "論文" or re.search(r"本論文|元論文|Intersection", mention[0], re.I)
            ):
                yield mention.start(), ref, ""


def citations(file, body):
    # Bare numbered paper references occur throughout Paper/ and the descent
    # modules. Outside these paths the paper must be identified explicitly.
    found = list(explicit(body))
    yield from found
    if PAPER_PATH.search(file):
        spans = [(pos, ref) for pos, ref, num in found if num]
        foreign = {pos for pos, ref in spans if ref != "論文"}
        # The same citation can occur with and without an explicit work name.
        # Deduplication uses the reference, number and physical source line.
        for pattern in (TYPED, DISPLAY, re.compile(r"(?<![\d.])3\.5[a-c](?![\w.])")):
            for match in pattern.finditer(body):
                if match.start() in foreign:
                    continue
                if pattern not in (TYPED, DISPLAY):
                    number = match[0]
                else:
                    number = normalize(match)
                if re.fullmatch(r"(?:§[34]|[§(]?[34]\.\d+[a-c]?\)?)", number):
                    # Skip mentions qualified by a different named reference.
                    line_prefix = body[body.rfind("\n", 0, match.start()) + 1:match.start()]
                    if re.search(r"(?:HTT|HA|Kerodon|Stacks|DAG|Lurie)\s*[,.:]?\s*$", line_prefix):
                        continue
                    yield match.start(), "論文", number


def main(repo, output):
    paths = subprocess.check_output(["git", "-C", str(repo), "ls-files", "-z", "--", "*.lean"])
    rows = set()
    for path in paths.decode().split("\0"):
        if not path:
            continue
        source = (repo / path).read_text(encoding="utf-8")
        for start, body in docstrings(source):
            first_line = source.count("\n", 0, start) + 1
            for offset, ref, number in citations(path, body):
                line = first_line + body.count("\n", 0, offset)
                rows.add((path, line, ref, number))
    writer = csv.writer(output, lineterminator="\n")
    writer.writerow(("file", "line", "reference", "number"))
    writer.writerows(sorted(rows))


if __name__ == "__main__":
    main(Path(sys.argv[1]), sys.stdout)
