import Verso
import VersoManual
import VersoBlueprint
import VersoBlueprint.Commands.Graph
import VersoBlueprint.Commands.Summary
import SerreBlueprint.Paper.Section1
import SerreBlueprint.Paper.Section2
import SerreBlueprint.Paper.Section3
import SerreBlueprint.Paper.Section4
import SerreBlueprint.Paper.Section5
import SerreBlueprint.Kerodon.Section1_1
import SerreBlueprint.Kerodon.Section1_2
import SerreBlueprint.Kerodon.Section1_3
import SerreBlueprint.Kerodon.Section1_4
import SerreBlueprint.Kerodon.Section1_5

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "SerrePositivity ブループリント（試作）" =>
%%%
tag := "serre-blueprint"
%%%

本論文（OpenAI, Positivity of Serre's Intersection Multiplicity, 2026-09-23）と、本体が使う文献（試作では Kerodon 第 1 章）の項目ごとに、SerrePositivity と Mathlib の対応する Lean の宣言を結んだブループリント。
各ノードの本文は対応表（`research/paper-coverage`・`research/kerodon-coverage`）の照合の理由（日本語の要約）で、原典の本文の写しではない。
Lean の宣言に結ぶのは、本論文では状態が own のもの、Kerodon では own・mathlib・both のものだけ。未証明の入力に依存するもの（interface）・一部（partial）は本文に宣言名を挙げる。
章のファイルは `blueprint/scripts/gen_paper.py`・`gen_kerodon.py` が対応表から生成する。手で直さない。

# 本論文
%%%
number := false
tag := "paper"
%%%

{include 1 SerreBlueprint.Paper.Section1}
{include 1 SerreBlueprint.Paper.Section2}
{include 1 SerreBlueprint.Paper.Section3}
{include 1 SerreBlueprint.Paper.Section4}
{include 1 SerreBlueprint.Paper.Section5}

# Kerodon 第 1 章 The Language of ∞-Categories
%%%
number := false
tag := "kerodon-1"
%%%

{include 1 SerreBlueprint.Kerodon.Section1_1}
{include 1 SerreBlueprint.Kerodon.Section1_2}
{include 1 SerreBlueprint.Kerodon.Section1_3}
{include 1 SerreBlueprint.Kerodon.Section1_4}
{include 1 SerreBlueprint.Kerodon.Section1_5}

{blueprint_graph}
{blueprint_summary}
