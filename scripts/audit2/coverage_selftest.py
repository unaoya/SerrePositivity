#!/usr/bin/env python3
"""Regression tests for exact reference resolution, fingerprint gates and links."""
import csv
import json
import os
from pathlib import Path
import sqlite3
import tempfile
from unittest.mock import patch

from audit import Failure, SCHEMA, command
from coverage import Index, compare, location, update_locations
from coverage_blueprint import generate, verify_output
from common import Resolver


def table():
    db = sqlite3.connect(":memory:")
    db.row_factory = sqlite3.Row
    db.executescript(SCHEMA)
    for module in ("SerrePositivity.A", "SerrePositivity.B"):
        db.execute("INSERT INTO module VALUES (?, '', '[]', 0)", (module,))
    def add(module, name, kind="thm", typ="type", value="value", refs=(), used=()):
        db.execute("INSERT INTO decl VALUES (" + ",".join(["?"]*20) + ")", (
            module,name,kind,1,0,0,typ,value,json.dumps(refs),json.dumps(used),"[]","[]","[]",
            0,None,0,0,"[3,0,7,0,5,4,5,12]","[]","fixture"))
    add("SerrePositivity.A", "Demo.statement", refs=["Demo.helper","Demo.fact"])
    add("SerrePositivity.A", "Demo.helper", kind="def", used=["Demo.inner"])
    add("SerrePositivity.A", "Demo.inner", kind="def", value="oldBody")
    add("SerrePositivity.A", "Demo.fact", used=["Demo.ignored"])
    add("SerrePositivity.B", "Demo.ignored", kind="def")
    add("SerrePositivity.B", "Other.Short")
    return db


def row(index, raw):
    verdict, found, candidates = index.resolve(raw)
    result = dict(file="research/demo-coverage/items.csv",item="1",ordinal=1,line=2,
                  column="declarations",raw=raw,status="own",partial_kind="",reason="理由",
                  literature="demo",edition="版1",reviewer="fixture",resolution=verdict,
                  candidates=json.dumps(candidates))
    if found:
        result.update(module=found["module"],name=found["name"],type_hash=found["type_hash"],
                      meaning_hash=index.meaning(found["module"],found["name"]),
                      location=location(found),public=1)
    return result


def verdict(old, new, moves=None, strict=True):
    result = compare([old],[new] if new else [],moves or {},strict)
    return result["pass_"], [r["verdict"] for r in result["changes"]]


def main():
    db = table()
    ext = {"pin":"fixed", "rows":[dict(module="Mathlib.Demo",name="Fact.external",
                                      type_hash="ext",public=True,location=[0,0,0,10,0,0,0,10],
                                      type_refs=[],kind="thm")]}
    index = lambda: Index(db,ext)
    source = "Demo.statement（注記） @ SerrePositivity/A.lean:6"
    old = row(index(),source)
    assert verdict(old,old) == (True,[])
    assert old["location"] == "SerrePositivity/A.lean:6"
    assert index().resolve("Fact.external @ Mathlib/Demo.lean:1")[0]=="external"
    assert index().resolve("Fact.absent @ Mathlib/Demo.lean:1")[0]=="missing"
    assert verdict(old,None)==(False,["deleted"])
    missing=row(index(),"No.suchName")
    assert verdict(old,missing)==(False,["deleted"])
    short=row(index(),"Short @ SerrePositivity/A.lean:6")
    assert short["resolution"]=="missing" and "Other.Short" in short["candidates"]
    assert verdict(old,short)==(False,["deleted"])
    assert index().resolve("Demo.statement @ SerrePositivity/B.lean:6")[0]=="missing"
    db.execute("INSERT INTO decl SELECT 'SerrePositivity.B',name,kind,public,private,internal,"
               "type_hash,value_hash,type_refs,value_refs,ctors,saved_axioms,instances,unsafe,"
               "implemented_by,extern,partial,location,axioms,source FROM decl WHERE name='Demo.statement'")
    assert index().resolve("Demo.statement")[0]=="ambiguous"
    db.execute("DELETE FROM decl WHERE module='SerrePositivity.B' AND name='Demo.statement'")
    db.execute("UPDATE decl SET type_hash='changed' WHERE name='Demo.statement'")
    typed = row(index(),source)
    assert verdict(old,typed)==(False,["statement-changed"])
    assert verdict(old,typed,strict=False)==(True,["statement-changed"])
    db.execute("UPDATE decl SET type_hash='type' WHERE name='Demo.statement'")
    db.execute("UPDATE decl SET value_hash='newBody' WHERE name='Demo.inner'")
    assert verdict(old,row(index(),source))==(False,["meaning-changed"])
    db.execute("UPDATE decl SET value_hash='oldBody' WHERE name='Demo.inner'")
    db.execute("UPDATE decl SET value_hash='proofChanged' WHERE name='Demo.fact'")
    assert verdict(old,row(index(),source))==(True,[])
    a=("SerrePositivity.A","Demo.statement")
    b=("SerrePositivity.B","Demo.statement")
    db.execute("UPDATE decl SET module=? WHERE name=?",b)
    moved=row(index(),"Demo.statement @ SerrePositivity/B.lean:6")
    assert verdict(old,moved)==(False,["unapproved-move"])
    assert verdict(old,moved,{a:b})==(True,["approved-move"])
    c=("SerrePositivity.B","Demo.renamed")
    db.execute("UPDATE decl SET name=? WHERE name=?",(c[1],b[1]))
    renamed=row(index(),"Demo.renamed（注記） @ SerrePositivity/B.lean:6")
    assert verdict(old,renamed)==(False,["unapproved-move"])
    assert verdict(old,renamed,{a:c})==(True,["approved-move"])

    with tempfile.TemporaryDirectory(prefix="audit2-coverage-") as tmp:
        root=Path(tmp)
        target=root/old["file"]
        target.parent.mkdir(parents=True)
        target.write_text("number,status,declarations,reason\n1,own," + source + ",理由\n")
        origin = dict(old, commit="old", baseline_note="fixture")
        outcome=compare([origin],[renamed],{a:c},True)
        update_locations(root,{"commit":"new"},[origin],outcome["changes"])
        parsed,=csv.DictReader(target.open())
        assert parsed["declarations"]=="Demo.renamed（注記） @ SerrePositivity/B.lean:6"
        assert parsed["status"]=="own" and parsed["reason"]=="理由"
        updated,=csv.DictReader((target.parent/"baseline.csv").open())
        assert updated["name"]==c[1] and updated["commit"]=="new"

        plan=root/"plan.json"
        raw="Demo.statement"
        plan.write_text(json.dumps(dict(root=str(root.resolve()), preview=False, commit="test",
                                        input_hash="hash", inputs={}, links={
                                            raw:["Demo.statement",a[0]],"Demo.second":["Demo.second",a[0]]})))
        cwd=Path.cwd()
        try:
            os.chdir(root)
            with patch.dict(os.environ,AUDIT2_BLUEPRINT_PLAN=str(plan)):
                writer=Resolver()
                writer.links("demo",raw+" | Demo.second",set(),True)
                try:
                    writer.write("output.lean",':::theorem "demo" (lean := "Demo.statement")\n')
                except SystemExit as error:
                    assert "Wrong blueprint links" in str(error)
                else:
                    raise AssertionError("one lost link was accepted")
                assert not (root/"output.lean").exists()
                writer.write("output.lean",':::theorem "demo" (lean := "Demo.statement, Demo.second")\n')
                assert (root/"output.lean").read_text().startswith("-- audit2: test inputs sha256 hash\n")
        finally:
            os.chdir(cwd)
        broken=dict(missing,literature="paper",file="research/paper-coverage/review/ch1.csv")
        try:
            generate(dict(commit=command(["git","rev-parse","HEAD"]),inputs={},references=[broken]),
                     root/"preflight",False,False)
        except Failure as error:
            assert "unresolved or non-public" in str(error)
        else:
            raise AssertionError("generation started with an unresolved reference")
        assert not (root/"preflight/tree").exists()
        expected = dict(old, literature="paper", file="research/paper-coverage/review/ch1.csv")
        for wrong in ({}, {"paper_1":["Section1.lean",[]]}):
            try:
                verify_output(wrong, [expected])
            except Failure:
                pass
            else:
                raise AssertionError("missing planned card or planned link was accepted")
    print("PASS: approved/unapproved move and rename, deletion, statement/body, proof stop, "
          "short name and owner ambiguity, pinned name, one lost link, pre-generation rejection")


if __name__=="__main__":
    main()
