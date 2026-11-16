import Verso
import VersoManual
import VersoBlueprint
import VersoBlueprint.Commands.Graph
import VersoBlueprint.Commands.Summary
import KerodonBlueprint.Chapters.Section1_1
import KerodonBlueprint.Chapters.Section1_2
import KerodonBlueprint.Chapters.Section1_3
import KerodonBlueprint.Chapters.Section1_4
import KerodonBlueprint.Chapters.Section1_5

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Kerodon に沿った形式化（試作：第 1 章）" =>

Kerodon（Lurie）の第 1 章「The Language of ∞-Categories」の項目ごとに、SerrePositivity と Mathlib の対応する Lean の宣言を結んだブループリント。
各ノードの本文は、対応表 `research/kerodon-coverage` の判定の理由（日本語の要約）で、Kerodon の本文の写しではない。番号から Kerodon の Tag へリンクする。
状態が own・mathlib・both で宣言が一意に解決できたものだけを Lean の宣言に結んでいる（partial は本文に宣言名を挙げるだけ）。
章のファイルは `blueprint/kerodon/scripts/gen_chapter.py` が対応表から生成する。手で直さない。

{include 0 KerodonBlueprint.Chapters.Section1_1}
{include 0 KerodonBlueprint.Chapters.Section1_2}
{include 0 KerodonBlueprint.Chapters.Section1_3}
{include 0 KerodonBlueprint.Chapters.Section1_4}
{include 0 KerodonBlueprint.Chapters.Section1_5}

{blueprint_graph}
{blueprint_summary}
