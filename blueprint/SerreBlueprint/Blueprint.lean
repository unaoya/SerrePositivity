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
import SerreBlueprint.Paper.External
import SerreBlueprint.Paper.Supplement
import SerreBlueprint.CLMST.Section1
import SerreBlueprint.CLMST.Section2
import SerreBlueprint.CLMST.Section3
import SerreBlueprint.CLMST.Section4
import SerreBlueprint.CLMST.Section5
import SerreBlueprint.CLMST.Section6
import SerreBlueprint.CLMST.Section7
import SerreBlueprint.CLMST.Section8
import SerreBlueprint.BS.Section1
import SerreBlueprint.BS.Section2
import SerreBlueprint.BS.Section3
import SerreBlueprint.BS.Section4
import SerreBlueprint.BS.Section5
import SerreBlueprint.BS.Section6
import SerreBlueprint.BS.Section7
import SerreBlueprint.BS.Section8
import SerreBlueprint.BS.Section9
import SerreBlueprint.BS.Section10
import SerreBlueprint.BS.Section11
import SerreBlueprint.BS.Section12
import SerreBlueprint.BS.Section13
import SerreBlueprint.BS.Section14
import SerreBlueprint.BS.Section15
import SerreBlueprint.BS.Section16
import SerreBlueprint.BS.Section17
import SerreBlueprint.BS.Section18
import SerreBlueprint.VDescent.BS17
import SerreBlueprint.VDescent.BM18
import SerreBlueprint.VDescent.Rydh
import SerreBlueprint.Kerodon.Section1_1
import SerreBlueprint.Kerodon.Section1_2
import SerreBlueprint.Kerodon.Section1_3
import SerreBlueprint.Kerodon.Section1_4
import SerreBlueprint.Kerodon.Section1_5
import SerreBlueprint.Kerodon.Section2_1
import SerreBlueprint.Kerodon.Section2_2
import SerreBlueprint.Kerodon.Section2_3
import SerreBlueprint.Kerodon.Section2_4
import SerreBlueprint.Kerodon.Section2_5
import SerreBlueprint.Kerodon.Section3_1
import SerreBlueprint.Kerodon.Section3_2
import SerreBlueprint.Kerodon.Section3_3
import SerreBlueprint.Kerodon.Section3_4
import SerreBlueprint.Kerodon.Section3_5
import SerreBlueprint.Kerodon.Section3_6
import SerreBlueprint.Kerodon.Section4_1
import SerreBlueprint.Kerodon.Section4_2
import SerreBlueprint.Kerodon.Section4_3
import SerreBlueprint.Kerodon.Section4_4
import SerreBlueprint.Kerodon.Section4_5
import SerreBlueprint.Kerodon.Section4_6
import SerreBlueprint.Kerodon.Section4_7
import SerreBlueprint.Kerodon.Section4_8
import SerreBlueprint.Kerodon.Section4_9
import SerreBlueprint.Kerodon.Section5_1
import SerreBlueprint.Kerodon.Section5_2
import SerreBlueprint.Kerodon.Section5_3
import SerreBlueprint.Kerodon.Section5_4
import SerreBlueprint.Kerodon.Section5_5
import SerreBlueprint.Kerodon.Section5_6
import SerreBlueprint.Kerodon.Section6_1
import SerreBlueprint.Kerodon.Section6_2
import SerreBlueprint.Kerodon.Section6_3
import SerreBlueprint.Kerodon.Section7_1
import SerreBlueprint.Kerodon.Section7_2
import SerreBlueprint.Kerodon.Section7_3
import SerreBlueprint.Kerodon.Section7_4
import SerreBlueprint.Kerodon.Section7_5
import SerreBlueprint.Kerodon.Section7_6
import SerreBlueprint.Kerodon.Section7_7
import SerreBlueprint.Kerodon.Section8_1
import SerreBlueprint.Kerodon.Section8_2
import SerreBlueprint.Kerodon.Section8_3
import SerreBlueprint.Kerodon.Section8_4
import SerreBlueprint.Kerodon.Section8_5
import SerreBlueprint.Kerodon.Section8_6
import SerreBlueprint.Kerodon.Section8_7
import SerreBlueprint.Kerodon.Section9_1
import SerreBlueprint.Kerodon.Section9_2
import SerreBlueprint.Kerodon.Section9_3
import SerreBlueprint.Kerodon.Section9_4
import SerreBlueprint.Kerodon.Section9_5
import SerreBlueprint.Kerodon.Section9_6
import SerreBlueprint.Kerodon.Section9_7
import SerreBlueprint.Kerodon.Section10_1
import SerreBlueprint.Kerodon.Section10_2

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "SerrePositivity ブループリント" =>
%%%
tag := "serre-blueprint"
%%%

本論文（OpenAI, Positivity of Serre's Intersection Multiplicity, 2026-09-23）と、本論文と本体が使う文献の項目ごとに、SerrePositivity と Mathlib の対応する Lean の宣言を結んだブループリント。
各ノードの本文は対応表（`research/` の各 `-coverage`）の照合の理由（日本語の要約）と解説の原稿で、原典の本文の写しではない。
各ノードの頭の「主張」は原典の主張の要約（`statements.csv`）、その下は対応表の照合の理由。対応表の状態が「なし」でない項目は Lean の宣言に結ぶ。一部（原典どおりではない）・未証明の入力に依存するものは、カードの札と依存グラフの色で見分ける。
章のファイルと、この入口は `blueprint/scripts/` の生成器が対応表から作る。手で直さない。

*部ごとの目標と状態*

- 本論文：主定理（Theorem 1.1、Serre の交点重複度の正値性）。75 項目（本体 37、一部 8、未証明の入力に依存 13、なし 17）
- CLMST（Cai–Lee–Ma–Schwede–Tucker, Perfectoid signature, perfectoid Hilbert–Kunz multiplicity, …, arXiv 2209.04046v4）：本論文が使う正規化長と perfectoid の重複度の結果（§2.2 ほか）。147 項目（本体 4、一部 20、未証明の入力に依存 6、なし 117）
- BS（Bhatt–Scholze, Prisms and prismatic cohomology、著者版）：本論文と CLMST が使う perfectoid 化（§7・§8）と、その土台の δ 環・prism（§2・§3）。211 項目（本体 25、一部 46、未証明の入力に依存 6、なし 134）
- v 降下（目標：BS17 Theorem 4.1 (i) と BM18 Proposition 4.8。BS17・BM18・Rydh の必要な項目）：BS17 Theorem 4.1 (i) と BM18 Proposition 4.8（BS Proposition 8.10 の arc 層性の入力）。49 項目（本体 10、Mathlib 3、一部 36）
- Kerodon 第 1 章 The Language of ∞-Categories：∞ 圏の基礎（本体の `InfinityCategories` の定義・定理の出どころ）。目標は章ごとには立てていない。180 項目（本体 20、Mathlib 83、両方 9、一部 18、なし 50）
- Kerodon 第 2 章 Examples of ∞-Categories：∞ 圏の基礎（本体の `InfinityCategories` の定義・定理の出どころ）。目標は章ごとには立てていない。213 項目（本体 19、Mathlib 40、一部 33、なし 121）
- Kerodon 第 3 章 Kan Complexes：∞ 圏の基礎（本体の `InfinityCategories` の定義・定理の出どころ）。目標は章ごとには立てていない。339 項目（本体 48、Mathlib 17、一部 42、なし 232）
- Kerodon 第 4 章 The Homotopy Theory of ∞-Categories：∞ 圏の基礎（本体の `InfinityCategories` の定義・定理の出どころ）。目標は章ごとには立てていない。588 項目（本体 104、Mathlib 36、一部 130、なし 318）
- Kerodon 第 5 章 Fibrations of ∞-Categories：∞ 圏の基礎（本体の `InfinityCategories` の定義・定理の出どころ）。目標は章ごとには立てていない。345 項目（本体 45、Mathlib 6、一部 85、なし 209）
- Kerodon 第 6 章 Adjoint Functors：∞ 圏の基礎（本体の `InfinityCategories` の定義・定理の出どころ）。目標は章ごとには立てていない。145 項目（本体 16、Mathlib 20、一部 44、なし 65）
- Kerodon 第 7 章 Limits and Colimits：∞ 圏の基礎（本体の `InfinityCategories` の定義・定理の出どころ）。目標は章ごとには立てていない。519 項目（本体 53、Mathlib 3、一部 145、なし 318）
- Kerodon 第 8 章 The Yoneda Embedding：∞ 圏の基礎（本体の `InfinityCategories` の定義・定理の出どころ）。目標は章ごとには立てていない。483 項目（本体 38、Mathlib 8、一部 74、なし 363）
- Kerodon 第 9 章 Large ∞-Categories：∞ 圏の基礎（本体の `InfinityCategories` の定義・定理の出どころ）。目標は章ごとには立てていない。597 項目（本体 31、Mathlib 6、一部 137、なし 423）
- Kerodon 第 10 章 Exactness and Animation：∞ 圏の基礎（本体の `InfinityCategories` の定義・定理の出どころ）。目標は章ごとには立てていない。144 項目（本体 14、Mathlib 2、一部 10、なし 118）

# 本論文
%%%
number := false
tag := "part-paper"
%%%

{include 1 SerreBlueprint.Paper.Section1}
{include 1 SerreBlueprint.Paper.Section2}
{include 1 SerreBlueprint.Paper.Section3}
{include 1 SerreBlueprint.Paper.Section4}
{include 1 SerreBlueprint.Paper.Section5}
{include 1 SerreBlueprint.Paper.External}
{include 1 SerreBlueprint.Paper.Supplement}

# CLMST（Cai–Lee–Ma–Schwede–Tucker, Perfectoid signature, perfectoid Hilbert–Kunz multiplicity, …, arXiv 2209.04046v4）
%%%
number := false
tag := "part-clmst"
%%%

{include 1 SerreBlueprint.CLMST.Section1}
{include 1 SerreBlueprint.CLMST.Section2}
{include 1 SerreBlueprint.CLMST.Section3}
{include 1 SerreBlueprint.CLMST.Section4}
{include 1 SerreBlueprint.CLMST.Section5}
{include 1 SerreBlueprint.CLMST.Section6}
{include 1 SerreBlueprint.CLMST.Section7}
{include 1 SerreBlueprint.CLMST.Section8}

# BS（Bhatt–Scholze, Prisms and prismatic cohomology、著者版）
%%%
number := false
tag := "part-bs"
%%%

{include 1 SerreBlueprint.BS.Section1}
{include 1 SerreBlueprint.BS.Section2}
{include 1 SerreBlueprint.BS.Section3}
{include 1 SerreBlueprint.BS.Section4}
{include 1 SerreBlueprint.BS.Section5}
{include 1 SerreBlueprint.BS.Section6}
{include 1 SerreBlueprint.BS.Section7}
{include 1 SerreBlueprint.BS.Section8}
{include 1 SerreBlueprint.BS.Section9}
{include 1 SerreBlueprint.BS.Section10}
{include 1 SerreBlueprint.BS.Section11}
{include 1 SerreBlueprint.BS.Section12}
{include 1 SerreBlueprint.BS.Section13}
{include 1 SerreBlueprint.BS.Section14}
{include 1 SerreBlueprint.BS.Section15}
{include 1 SerreBlueprint.BS.Section16}
{include 1 SerreBlueprint.BS.Section17}
{include 1 SerreBlueprint.BS.Section18}

# v 降下（目標：BS17 Theorem 4.1 (i) と BM18 Proposition 4.8。BS17・BM18・Rydh の必要な項目）
%%%
number := false
tag := "part-vdescent"
%%%

{include 1 SerreBlueprint.VDescent.BS17}
{include 1 SerreBlueprint.VDescent.BM18}
{include 1 SerreBlueprint.VDescent.Rydh}

# Kerodon 第 1 章 The Language of ∞-Categories
%%%
number := false
tag := "part-kerodon-1"
%%%

{include 1 SerreBlueprint.Kerodon.Section1_1}
{include 1 SerreBlueprint.Kerodon.Section1_2}
{include 1 SerreBlueprint.Kerodon.Section1_3}
{include 1 SerreBlueprint.Kerodon.Section1_4}
{include 1 SerreBlueprint.Kerodon.Section1_5}

# Kerodon 第 2 章 Examples of ∞-Categories
%%%
number := false
tag := "part-kerodon-2"
%%%

{include 1 SerreBlueprint.Kerodon.Section2_1}
{include 1 SerreBlueprint.Kerodon.Section2_2}
{include 1 SerreBlueprint.Kerodon.Section2_3}
{include 1 SerreBlueprint.Kerodon.Section2_4}
{include 1 SerreBlueprint.Kerodon.Section2_5}

# Kerodon 第 3 章 Kan Complexes
%%%
number := false
tag := "part-kerodon-3"
%%%

{include 1 SerreBlueprint.Kerodon.Section3_1}
{include 1 SerreBlueprint.Kerodon.Section3_2}
{include 1 SerreBlueprint.Kerodon.Section3_3}
{include 1 SerreBlueprint.Kerodon.Section3_4}
{include 1 SerreBlueprint.Kerodon.Section3_5}
{include 1 SerreBlueprint.Kerodon.Section3_6}

# Kerodon 第 4 章 The Homotopy Theory of ∞-Categories
%%%
number := false
tag := "part-kerodon-4"
%%%

{include 1 SerreBlueprint.Kerodon.Section4_1}
{include 1 SerreBlueprint.Kerodon.Section4_2}
{include 1 SerreBlueprint.Kerodon.Section4_3}
{include 1 SerreBlueprint.Kerodon.Section4_4}
{include 1 SerreBlueprint.Kerodon.Section4_5}
{include 1 SerreBlueprint.Kerodon.Section4_6}
{include 1 SerreBlueprint.Kerodon.Section4_7}
{include 1 SerreBlueprint.Kerodon.Section4_8}
{include 1 SerreBlueprint.Kerodon.Section4_9}

# Kerodon 第 5 章 Fibrations of ∞-Categories
%%%
number := false
tag := "part-kerodon-5"
%%%

{include 1 SerreBlueprint.Kerodon.Section5_1}
{include 1 SerreBlueprint.Kerodon.Section5_2}
{include 1 SerreBlueprint.Kerodon.Section5_3}
{include 1 SerreBlueprint.Kerodon.Section5_4}
{include 1 SerreBlueprint.Kerodon.Section5_5}
{include 1 SerreBlueprint.Kerodon.Section5_6}

# Kerodon 第 6 章 Adjoint Functors
%%%
number := false
tag := "part-kerodon-6"
%%%

{include 1 SerreBlueprint.Kerodon.Section6_1}
{include 1 SerreBlueprint.Kerodon.Section6_2}
{include 1 SerreBlueprint.Kerodon.Section6_3}

# Kerodon 第 7 章 Limits and Colimits
%%%
number := false
tag := "part-kerodon-7"
%%%

{include 1 SerreBlueprint.Kerodon.Section7_1}
{include 1 SerreBlueprint.Kerodon.Section7_2}
{include 1 SerreBlueprint.Kerodon.Section7_3}
{include 1 SerreBlueprint.Kerodon.Section7_4}
{include 1 SerreBlueprint.Kerodon.Section7_5}
{include 1 SerreBlueprint.Kerodon.Section7_6}
{include 1 SerreBlueprint.Kerodon.Section7_7}

# Kerodon 第 8 章 The Yoneda Embedding
%%%
number := false
tag := "part-kerodon-8"
%%%

{include 1 SerreBlueprint.Kerodon.Section8_1}
{include 1 SerreBlueprint.Kerodon.Section8_2}
{include 1 SerreBlueprint.Kerodon.Section8_3}
{include 1 SerreBlueprint.Kerodon.Section8_4}
{include 1 SerreBlueprint.Kerodon.Section8_5}
{include 1 SerreBlueprint.Kerodon.Section8_6}
{include 1 SerreBlueprint.Kerodon.Section8_7}

# Kerodon 第 9 章 Large ∞-Categories
%%%
number := false
tag := "part-kerodon-9"
%%%

{include 1 SerreBlueprint.Kerodon.Section9_1}
{include 1 SerreBlueprint.Kerodon.Section9_2}
{include 1 SerreBlueprint.Kerodon.Section9_3}
{include 1 SerreBlueprint.Kerodon.Section9_4}
{include 1 SerreBlueprint.Kerodon.Section9_5}
{include 1 SerreBlueprint.Kerodon.Section9_6}
{include 1 SerreBlueprint.Kerodon.Section9_7}

# Kerodon 第 10 章 Exactness and Animation
%%%
number := false
tag := "part-kerodon-10"
%%%

{include 1 SerreBlueprint.Kerodon.Section10_1}
{include 1 SerreBlueprint.Kerodon.Section10_2}

{blueprint_graph}
{blueprint_summary}
