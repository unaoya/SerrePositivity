"""Rendering policy for the VersoBlueprint revision pinned by the blueprint."""
import json

from audit import Failure
from coverage import LIVE

BOOKS = {"paper", "clmst", "bs", "bs17", "bm18", "rydh", "kerodon", "htt", "ha"}
VERSO_PIN = "7bd0c10f0b77d75ab81fe2a2005f6a6428983d27"

# Data.lean: ConstantInfo.blueprintNodeKind? and ExternalRefSnapshot.lean:
# externalRefSnapshotWithStatus. Axioms and opaque declarations are accepted
# by the fallback in the latter, even though blueprintNodeKind? returns none.
NAME_ONLY_KINDS = {"ctor", "rec", "quot"}
LINK_KINDS = {"def", "thm", "inductive", "axiom", "opaque"}


def verify_pin(manifest):
    packages = json.loads(manifest.read_text())["packages"]
    if not any(p["name"] == "VersoBlueprint" and p.get("rev") == VERSO_PIN for p in packages):
        raise Failure("review the external reference policy for the new VersoBlueprint revision")


def is_link_row(row):
    if row["literature"] not in BOOKS or row["status"] not in LIVE:
        return False
    if row["file"].endswith("/external.csv"):
        return not row["item"].startswith("CLMST ")
    return "/review/" in row["file"]


def name_only(row):
    return row.get("kind") in NAME_ONLY_KINDS


def require_kind(row):
    if row.get("kind") not in NAME_ONLY_KINDS | LINK_KINDS:
        raise Failure(f"unknown Lean declaration kind for {row['name']}")


def name_only_report(references):
    rows = []
    fields = ("literature", "item", "file", "line", "ordinal", "name", "module", "kind")
    for row in references:
        if is_link_row(row) and row.get("name") and row["public"]:
            require_kind(row)
            if name_only(row):
                rows.append({k: row[k] for k in fields})
    return dict(verso_revision=VERSO_PIN, count=len(rows), references=rows)
