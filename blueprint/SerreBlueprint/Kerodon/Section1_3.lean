import Verso
import VersoManual
import VersoBlueprint
import Mathlib.Algebra.Category.MonCat.Basic
import Mathlib.Algebra.Category.Semigrp.Basic
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Semigroup
import Mathlib.AlgebraicTopology.SimplicialSet.HomotopyCat
import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
import Mathlib.AlgebraicTopology.SimplicialSet.NerveAdjunction
import Mathlib.AlgebraicTopology.SimplicialSet.Skeleton
import Mathlib.CategoryTheory.Core
import Mathlib.CategoryTheory.Groupoid
import Mathlib.CategoryTheory.PathCategory.Basic
import Mathlib.CategoryTheory.SingleObj
import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FromCategoriesToSimplicialSets.GroupNerveHomotopy
import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FromCategoriesToSimplicialSets.KanCharacterization
import SerrePositivity.KST.Comparison.BarSegal

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "1.3 From Categories to Simplicial Sets" =>
%%%
number := false
tag := "kerodon-1-3"
%%%

Kerodon の 1.3 節（[Tag 002L](https://kerodon.net/tag/002L)）の項目と、SerrePositivity・Mathlib の宣言との対応。本文は対応表（research/kerodon-coverage）の判定の理由の要約で、Kerodon の本文の写しではない。

# 1.3.1 The Nerve of a Category

%%%
number := false
tag := "kerodon-1-3-1"
%%%

Kerodon [Tag 002M](https://kerodon.net/tag/002M)

:::definition "kerodon_1_3_1_1" (lean := "CategoryTheory.nerve, CategoryTheory.nerveFunctor")
Kerodon Construction 1.3.1.1（[Tag 002N](https://kerodon.net/tag/002N)）。対応表の状態：Mathlib にある。

仮定：通常の圏 C と非負次数 n（Kerodon と一致）。結論：nerve C は次数 n で \[n\]→C に相当する可合成射列を取り、単体圏の射に沿う前合成で単体集合を作る（一致）。

:::

:::definition "kerodon_1_3_1_6" (lean := "SSet.skeleton, CategoryTheory.nerve")
Kerodon Variant 1.3.1.6（[Tag 03X2](https://kerodon.net/tag/03X2)）。対応表の状態：Mathlib にある。

仮定：圏 C と非負整数 n（Kerodon と一致）。結論：nerve C の skeleton (n+1) が次数 n 以下で生成された部分複体。n=0 の値は対象に対応する頂点とその退化でできる（一致）。

:::

# 1.3.2 Example: Monoids as Simplicial Sets

%%%
number := false
tag := "kerodon-1-3-2"
%%%

Kerodon [Tag 04FY](https://kerodon.net/tag/04FY)

:::definition "kerodon_1_3_2_1" (lean := "Monoid")
Kerodon Definition 1.3.2.1（[Tag 04FZ](https://kerodon.net/tag/04FZ)）。対応表の状態：Mathlib にある。

仮定：集合 M と二項演算（Kerodon と一致）。結論：Monoid M のデータは結合的な積と左右の単位元を含む（一致）。

:::

:::definition "kerodon_1_3_2_3" (lean := "MonoidHom, MonCat")
Kerodon Definition 1.3.2.3（[Tag 00BR](https://kerodon.net/tag/00BR)）。対応表の状態：Mathlib にある。

仮定：モノイド M,N（Kerodon と一致）。結論：MonoidHom は積と単位を保つ関数を与え、MonCat はそれを射とするモノイドの圏（一致）。

:::

:::definition "kerodon_1_3_2_5" (lean := "CategoryTheory.SingleObj, SerrePositivity.KST.Comparison.monoidWordSimplex")
Kerodon Construction 1.3.2.5（[Tag 04G0](https://kerodon.net/tag/04G0)）。対応表の状態：本体と Mathlib にある。

仮定：モノイド M（Kerodon と一致）。結論：nerve (SingleObj M) が一対象圏 BM の分類単体集合で、monoidWordSimplex は M の語に対応するその単体を作る（一致）。

:::

:::proposition "kerodon_1_3_2_7"
Kerodon Proposition 1.3.2.7（[Tag 04G2](https://kerodon.net/tag/04G2)）。対応表の状態：一部。

MonCat.toCatとnerveFunctorの充満忠実性はある。原文の本質的像の全次数Segal条件との同値は未対応。複数名の略記と名前空間を展開する。

宣言：`MonCat.toCat_full`、`MonCat.toCat_faithful`、`CategoryTheory.nerveFunctor.fullyfaithful`、`SerrePositivity.KST.Comparison.monoidWordSimplex`、`SerrePositivity.KST.Comparison.monoidWordLabels`

:::

:::definition "kerodon_1_3_2_8" (lean := "Semigroup, Semigrp, MulHom")
Kerodon Variant 1.3.2.8（[Tag 04G3](https://kerodon.net/tag/04G3)）。対応表の状態：Mathlib にある。

仮定：結合的乗法のある集合、二つのそのような構造の間の関数（Kerodon と一致）。結論：Semigroup は結合則、MulHom は積の保存を表し、Semigrp はその対象と射の圏（一致）。

:::

:::definition "kerodon_1_3_2_12"
Kerodon Variant 1.3.2.12（[Tag 04G6](https://kerodon.net/tag/04G6)）。対応表の状態：なし。

確認済み・なし（対象ソースの探索範囲内）。半単体集合と非単位的モノイドのbarを検索。Semigrpや単位的モノイドのnerveはあるが、非単位的モノイドの半単体barは見つからない。

:::

:::proposition "kerodon_1_3_2_14"
Kerodon Proposition 1.3.2.14（[Tag 04G8](https://kerodon.net/tag/04G8)）。対応表の状態：なし。

確認済み・なし（対象ソースの探索範囲内）。半単体bar・非単位的モノイドの圏の埋め込みを検索。一般の非単位的モノイドの埋め込みと本質的像の特徴づけは見つからない。

:::

# 1.3.3 Recovering a Category from its Nerve

%%%
number := false
tag := "kerodon-1-3-3"
%%%

Kerodon [Tag 002Y](https://kerodon.net/tag/002Y)

:::proposition "kerodon_1_3_3_1" (lean := "CategoryTheory.nerveFunctor.full, CategoryTheory.nerveFunctor.faithful, CategoryTheory.nerveFunctor.fullyfaithful")
Kerodon Proposition 1.3.3.1（[Tag 002Z](https://kerodon.net/tag/002Z)）。対応表の状態：Mathlib にある。

仮定：通常の圏とその間の関手（Kerodon と一致）。結論：nerveFunctor.full と faithful、さらに fullyfaithful が通常圏の nerve の充満忠実性を与える（一致）。

:::

# 1.3.4 Characterization of Nerves

%%%
number := false
tag := "kerodon-1-3-4"
%%%

Kerodon [Tag 0030](https://kerodon.net/tag/0030)

:::proposition "kerodon_1_3_4_1"
Kerodon Proposition 1.3.4.1（[Tag 0031](https://kerodon.net/tag/0031)）。対応表の状態：一部。

nerveのstrict Segal性と、それによるquasicategory性はある。strict Segalからnerveを復元する逆向きはMathlibのTODO。原文の一意内ホーン充填との同値全体ではない。

宣言：`CategoryTheory.Nerve.strictSegal`、`SSet.StrictSegal`

:::

:::lemma_ "kerodon_1_3_4_2"
Kerodon Lemma 1.3.4.2（[Tag 0032](https://kerodon.net/tag/0032)）。対応表の状態：一部。

一般のnerveの内ホーン充填存在はある。一意性の引用はQuiver.IsThin Cを追加仮定する特例。thinNerveの名前空間を補正。

宣言：`CategoryTheory.Nerve.strictSegal`、`SSet.StrictSegal.quasicategory`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.thinNerve_hom_ext_horn`

:::

:::lemma_ "kerodon_1_3_4_3"
Kerodon Lemma 1.3.4.3（[Tag 0033](https://kerodon.net/tag/0033)）。対応表の状態：なし。

確認済み・なし（対象ソースの探索範囲内）。一意内ホーン充填と頂点・辺の全単射からの同型を検索。StrictSegalのspineの全単射は個々の対象内の性質であり、原文の射に対する定理は見つからない。

:::

# 1.3.5 The Nerve of a Groupoid

%%%
number := false
tag := "kerodon-1-3-5"
%%%

Kerodon [Tag 0035](https://kerodon.net/tag/0035)

:::definition "kerodon_1_3_5_1" (lean := "CategoryTheory.Groupoid, CategoryTheory.IsGroupoid")
Kerodon Definition 1.3.5.1（[Tag 0036](https://kerodon.net/tag/0036)）。対応表の状態：Mathlib にある。

仮定：圏 C（Kerodon と一致）。結論：IsGroupoid C は全ての射が IsIso、すなわち両側逆を持つことを要求し、Groupoid は逆射を構造として持つ（一致）。

:::

:::proposition "kerodon_1_3_5_2" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FromCategoriesToSimplicialSets.groupoidNerve_kanComplex, SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FromCategoriesToSimplicialSets.kanComplex_iff_isGroupoid, CategoryTheory.nerveFunctorCompHoFunctorIso")
Kerodon Proposition 1.3.5.2（[Tag 0037](https://kerodon.net/tag/0037)）。対応表の状態：本体にある。

仮定：通常の圏 C（Kerodon と一致。Lean の nerve は Quasicategory インスタンスを持つ）。結論：groupoidNerve\_kanComplex は順方向。逆方向は kanComplex\_iff\_isGroupoid と nerveFunctorCompHoFunctorIso の hN(C)≅C で与えられる（一致）。

:::

:::definition "kerodon_1_3_5_4" (lean := "CategoryTheory.Core")
Kerodon Construction 1.3.5.4（[Tag 007G](https://kerodon.net/tag/007G)）。対応表の状態：Mathlib にある。

仮定：圏 C（Kerodon と一致）。結論：Core C は C の全対象を持ち、Hom を同型に制限した亜群（一致）。

:::

# 1.3.6 The Homotopy Category of a Simplicial Set

%%%
number := false
tag := "kerodon-1-3-6"
%%%

Kerodon [Tag 00HE](https://kerodon.net/tag/00HE)

:::definition "kerodon_1_3_6_1"
Kerodon Definition 1.3.6.1（[Tag 004J](https://kerodon.net/tag/004J)）。対応表の状態：一部。

hoFunctorとnerveAdjunctionは標準のホモトピー圏を構成する。任意の指定uが普遍性を満たすという述語はない。随伴の名前空間を補正。

宣言：`SSet.hoFunctor`、`CategoryTheory.nerveAdjunction`

:::

:::definition "kerodon_1_3_6_3" (lean := "SSet.HomotopyCategory, SSet.hoFunctor")
Kerodon Notation 1.3.6.3（[Tag 004K](https://kerodon.net/tag/004K)）。対応表の状態：Mathlib にある。

仮定：単体集合 S と、通常圏を求める普遍性（Lean が弱い：hoFunctor はすべての単体集合上で定義済み）。結論：HomotopyCategory S がホモトピー圏の値で、hoFunctor が S の射への作用を与える（一致。普遍性による同型の一意性は随伴から読む）。

:::

:::proposition "kerodon_1_3_6_4" (lean := "CategoryTheory.nerveAdjunction")
Kerodon Proposition 1.3.6.4（[Tag 004M](https://kerodon.net/tag/004M)）。対応表の状態：Mathlib にある。

仮定：任意の単体集合 S（Kerodon と一致）。結論：nerveAdjunction の単位 S ⟶ N(hS) と Hom 全単射が普遍的なホモトピー圏の存在を与える（一致）。

:::

:::corollary "kerodon_1_3_6_5" (lean := "CategoryTheory.nerveAdjunction")
Kerodon Corollary 1.3.6.5（[Tag 004N](https://kerodon.net/tag/004N)）。対応表の状態：Mathlib にある。

仮定：単体集合の圏と通常圏の圏（Kerodon と一致）。結論：nerveAdjunction は hoFunctor ⊣ nerveFunctor を与える（一致）。

:::

# 1.3.7 Example: The Path Category of a Directed Graph

%%%
number := false
tag := "kerodon-1-3-7"
%%%

Kerodon [Tag 00HJ](https://kerodon.net/tag/00HJ)

:::definition "kerodon_1_3_7_1" (lean := "CategoryTheory.Paths")
Kerodon Construction 1.3.7.1（[Tag 00HK](https://kerodon.net/tag/00HK)）。対応表の状態：Mathlib にある。

仮定：頂点型に Quiver 構造（Kerodon と一致）。結論：Paths の射は始点・終点を合わせて連結できる辺の有限列で、空列が恒等射、連結が合成（一致）。

:::

:::proposition "kerodon_1_3_7_5"
Kerodon Proposition 1.3.7.5（[Tag 00HP](https://kerodon.net/tag/00HP)）。対応表の状態：一部。

Paths.liftはquiverからの前関手を道の圏からの関手へ延長する。グラフに付随する1次元単体集合のホモトピー圏との比較はない。

宣言：`CategoryTheory.Paths.lift`

:::

:::definition "kerodon_1_3_7_7"
Kerodon Definition 1.3.7.7（[Tag 00HR](https://kerodon.net/tag/00HR)）。対応表の状態：一部。

Pathsはあるが、圏があるPathsと同型であるという自由性の述語は引用されていない。

宣言：`CategoryTheory.Paths`

:::

:::definition "kerodon_1_3_7_8"
Kerodon Definition 1.3.7.8（[Tag 00HS](https://kerodon.net/tag/00HS)）。対応表の状態：なし。

確認済み・なし（対象ソースの探索範囲内）。indecomposable morphism/arrowと圏の自由性を検索。対象の直和非分解性とは異なる、原文の射の分解に関する述語は見つからない。

:::

:::proposition "kerodon_1_3_7_11"
Kerodon Proposition 1.3.7.11（[Tag 00HV](https://kerodon.net/tag/00HV)）。対応表の状態：なし。

確認済み・なし（対象ソースの探索範囲内）。free category・自由圏・既約射の表示を検索。Pathsの普遍性と道の帰納法はあるが、原文の自由性の5条件の同値は見つからない。

:::

