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

*定義 3.2 （半順序集合の脈体）*

半順序集合 $`P` について、単体的集合 $`N(P)` を、$`N(P)([m])` を順序を保つ写像 $`[m]\to P` の全体とし、$`\theta\colon[m]\to[m']` には前合成で作用させて定める。

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

原文の充満忠実な埋込みという結論は MonCat.toCat の Full/Faithful と nerveFunctor の FullyFaithful の合成から直接得られる。さらに monoidWordEquiv は実際のモノイドの神経の n 単体を Fin n→T に同定する。任意SがSegal条件からその本質的像に入る逆は含めない。

宣言：`MonCat.toCat_full`、`MonCat.toCat_faithful`、`CategoryTheory.nerveFunctor.fullyfaithful`、`SerrePositivity.KST.Comparison.monoidWordSimplex`、`SerrePositivity.KST.Comparison.monoidWordLabels`、`SerrePositivity.KST.Comparison.monoidWordEquiv`

:::

:::definition "kerodon_1_3_2_8" (lean := "Semigroup, Semigrp, MulHom")
Kerodon Variant 1.3.2.8（[Tag 04G3](https://kerodon.net/tag/04G3)）。対応表の状態：Mathlib にある。

仮定：結合的乗法のある集合、二つのそのような構造の間の関数（Kerodon と一致）。結論：Semigroup は結合則、MulHom は積の保存を表し、Semigrp はその対象と射の圏（一致）。

:::

:::definition "kerodon_1_3_2_12"
Kerodon Variant 1.3.2.12（[Tag 04G6](https://kerodon.net/tag/04G6)）。対応表の状態：なし。

原文は単位を仮定しないモノイドの半単体的barとその面の式。semi-simplicial/nonunital barを再検索。通常のMonCatのmonoidWordEquivは単位を持つ圏のnerveであり、非単位的モノイドの同じ半単体関手の構成ではない。

:::

:::proposition "kerodon_1_3_2_14"
Kerodon Proposition 1.3.2.14（[Tag 04G8](https://kerodon.net/tag/04G8)）。対応表の状態：なし。

原文は非単位的モノイドのbarの半単体集合への充満忠実性と本質的像。nonunital bar/semisimplicialで再検索。単位付きモノイドを通常の圏の神経へ埋める宣言と、その対象上のSegal座標だけでは、原文の別の始域・終域の関手の結論を直接与えない。

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

:::proposition "kerodon_1_3_4_1" (uses := "kerodon_1_1_0_6, kerodon_1_3_3_1, kerodon_1_3_4_2, kerodon_1_3_4_3")
Kerodon Proposition 1.3.4.1（[Tag 0031](https://kerodon.net/tag/0031)）。対応表の状態：なし。

原文の特徴づけは全ての内hornの一意充填との iff。nerve の StrictSegal は spine 座標の全単射で、引用型には内hornの一意充填もその逆の再構成もない。StrictSegalから任意内hornの充填・一意性へ移す証明を要するため、必要方向と数えない。

宣言：`CategoryTheory.Nerve.strictSegal`、`SSet.StrictSegal`

:::

:::lemma_ "kerodon_1_3_4_2" (uses := "kerodon_1_1_0_6, kerodon_1_3_4_1")
Kerodon Lemma 1.3.4.2（[Tag 0032](https://kerodon.net/tag/0032)）。対応表の状態：一部。

原文は任意圏の nerve の内hornの一意充填。Quasicategory 性から充填の存在、thinNerve\_hom\_ext\_horn から2次元以上の任意horn制限の単射性を直接組み合わせ、Quiver.IsThin C を追加した場合の同じ一意充填を得る。一般圏の一意性はこの引用にない。

宣言：`CategoryTheory.Nerve.strictSegal`、`SSet.StrictSegal.quasicategory`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.thinNerve_hom_ext_horn`

:::

:::lemma_ "kerodon_1_3_4_3" (uses := "kerodon_1_1_0_6, kerodon_1_1_3_1, kerodon_1_1_4_12, kerodon_1_3_4_1")
Kerodon Lemma 1.3.4.3（[Tag 0033](https://kerodon.net/tag/0033)）。対応表の状態：なし。

原文は一意内horn充填を持つ二つのSSet間のfを頂点・辺の全単射から同型とする。nerve/isIso/Segal/bijectiveで再検索。nerveAdjunctionの余単位の同型や特定のnerve比較は別の射で、任意のこのfに対する判定ではない。

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

:::definition "kerodon_1_3_6_1" (uses := "kerodon_1_1_0_6, kerodon_1_3_3_1")
Kerodon Definition 1.3.6.1（[Tag 004J](https://kerodon.net/tag/004J)）。対応表の状態：なし。

原文は任意の指定u:S→N(C)が全Dへの合成でHom全単射を満たすという普遍性の述語。hoFunctorとnerveAdjunctionは標準のモデルと随伴で、任意uに関するこの述語そのものではない。標準モデルの構成を別の定義の一部とはしない。

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

:::proposition "kerodon_1_3_7_5" (uses := "kerodon_1_1_0_6, kerodon_1_3_6_1")
Kerodon Proposition 1.3.7.5（[Tag 00HP](https://kerodon.net/tag/00HP)）。対応表の状態：なし。

原文は指定u:G\_•→N(Path\[G\])によるHom全単射。Paths.lift はquiverの前関手を道の圏へ延長するだけで、単体集合G\_•からの射との同定や指定uとの合成を型に持たない。追加の比較が必要な証明部品。

宣言：`CategoryTheory.Paths.lift`

:::

:::definition "kerodon_1_3_7_7"
Kerodon Definition 1.3.7.7（[Tag 00HR](https://kerodon.net/tag/00HR)）。対応表の状態：なし。

原文は任意圏CがあるPath\[G\]と同型という自由性の述語。Pathsは対象型の別名とその道の圏構造を作る構成であり、その述語の直接の宣言ではない。

宣言：`CategoryTheory.Paths`

:::

:::definition "kerodon_1_3_7_8"
Kerodon Definition 1.3.7.8（[Tag 00HS](https://kerodon.net/tag/00HS)）。対応表の状態：なし。

原文は圏の非恒等射の全ての2因子分解でどちらかが恒等となるというindecomposableの述語。indecomposable morphism・Paths/freeCategoryで再検索。対象の非直和分解性や自由道の長さは別の述語で、この任意圏の射の定義は見つからない。

:::

:::proposition "kerodon_1_3_7_11"
Kerodon Proposition 1.3.7.11（[Tag 00HV](https://kerodon.net/tag/00HV)）。対応表の状態：なし。

原文は自由圏・既約射グラフからの標準関手の同型/同値/充満忠実性・既約分解の一意性の5条件 iff。freeCategory/Paths/indecomposableで再検索。Paths.liftの延長普遍性だけでは、原文の既約射グラフと指定関手を直接扱わず追加構成を要する。

:::

