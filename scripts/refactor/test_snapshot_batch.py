import json
from pathlib import Path
from subprocess import CompletedProcess
from tempfile import TemporaryDirectory
import unittest
from unittest.mock import patch

import snapshot_batch as batch


class BatchTests(unittest.TestCase):
    def test_group_boundaries_and_coverage(self):
        modules = ([f"SerrePositivity.EInfinity.M{i}" for i in range(35)]
                   + [f"SerrePositivity.EInfinityExtra.M{i}" for i in range(70)])
        shards = list(batch.groups(modules))
        self.assertEqual([len(s) for s in shards], [16, 16, 3, 64, 6])
        self.assertEqual(sum(shards, []), modules)

    def test_memory_retry_preserves_coverage(self):
        with TemporaryDirectory() as temp:
            root = Path(temp)
            mapping = root/"names.json"
            mapping.write_text("{}")
            modules = ["A", "B"]
            for name in modules:
                (root/(name + ".lean")).write_text("module\n")
            def snapshot(args, cwd, stdout, stderr):
                names = args[args.index("--modules") + 1].split(",")
                self.assertEqual(args[args.index("-M") + 1], "40000")
                self.assertEqual(args[args.index("--name-map") + 1], str(mapping))
                if len(names) > 1:
                    return CompletedProcess(args, 137)
                Path(args[-1]).write_text(json.dumps(dict(schema_version=2, name_map={}, modules=names,
                    declarations=[], count=0, huge_terms=[], hash_algorithm="normalized Expr DAG mixHash v1", sources=[dict(module=names[0], source="module\n")])))
                return CompletedProcess(args, 0)
            with patch.object(batch, "ROOT", root), patch.object(batch.subprocess, "run", snapshot):
                batch.collect(modules, mapping, root/"shards")
            state = json.loads((root/"shards/manifest.json").read_text())
            self.assertEqual((state["status"], state["completed"]), ("PASS", 2))
            self.assertEqual([item["exit_code"] for item in state["attempts"]], [137, 0, 0])

    def test_other_failures_do_not_retry(self):
        self.assertFalse(batch.memory_failure(1, "unknown module"))
        self.assertTrue(batch.memory_failure(1, "maximum memory consumption exceeded"))
