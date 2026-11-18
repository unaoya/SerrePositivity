import Verso
import VersoManual
import VersoBlueprint
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.Bicategory.Adjunction.Basic
import Mathlib.CategoryTheory.Bicategory.Adjunction.Mate
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.Adjunction
import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjunctionsInTwoCategories.AdjunctionUnitInvertible
import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjunctionsInTwoCategories.HomCorrespondence
import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjunctionsInTwoCategories.UnitHomCriterion

open Verso.Genre
open Verso.Genre.Manual
open Informal

-- 章が長いと既定の上限で時間切れになる（本論文 §5、11-18）
set_option maxHeartbeats 2000000

#doc (Manual) "6.1 Adjunctions in 2-Categories" =>
%%%
number := false
tag := "kerodon-6-1"
%%%

Kerodon の 6.1 節（[Tag 02CA](https://kerodon.net/tag/02CA)）の項目と、SerrePositivity・Mathlib の宣言との対応。本文は対応表（research/kerodon-coverage）の判定の理由の要約で、Kerodon の本文の写しではない。

:::definition "kerodon_6_1_0_1" (lean := "CategoryTheory.Adjunction.CoreHomEquiv, CategoryTheory.Adjunction.mkOfHomEquiv")
Kerodon Definition 6.1.0.1（[Tag 02CB](https://kerodon.net/tag/02CB)）。対応表の状態：Mathlib にある。

仮定：通常の圏 C,D と F:C→D、G:D→C（Kerodon と一致）。結論：CoreHomEquiv は Hom(Fx,y)≃Hom(x,Gy) と両変数の自然性を束ね、Adjunction に変換できる（一致）。

:::

:::definition "kerodon_6_1_0_2" (lean := "CategoryTheory.Adjunction, CategoryTheory.Adjunction.mkOfUnitCounit")
Kerodon Definition 6.1.0.2（[Tag 02CC](https://kerodon.net/tag/02CC)）。対応表の状態：Mathlib にある。

仮定：通常の圏 C,D と F:C→D、G:D→C（Kerodon と一致）。結論：Adjunction は単位 id→F⋙G、余単位 G⋙F→id と二つの三角恒等式を束ねる（一致）。

:::

# 6.1.1 Adjunctions

%%%
number := false
tag := "kerodon-6-1-1"
%%%

Kerodon [Tag 02CF](https://kerodon.net/tag/02CF)

:::definition "kerodon_6_1_1_1" (lean := "CategoryTheory.Bicategory.Adjunction")
Kerodon Definition 6.1.1.1（[Tag 02CG](https://kerodon.net/tag/02CG)）。対応表の状態：Mathlib にある。

仮定：双圏 B、対象 a,b と 1 射 f:a→b、g:b→a（Kerodon と一致）。結論：Bicategory.Adjunction f g は単位・余単位の 2 射と unitor・associator を含む左右の三角恒等式（一致）。

:::

# 6.1.2 Adjuncts

%%%
number := false
tag := "kerodon-6-1-2"
%%%

Kerodon [Tag 02CP](https://kerodon.net/tag/02CP)

:::definition "kerodon_6_1_2_1" (lean := "CategoryTheory.Bicategory.Adjunction.homEquiv₂, SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjunctionsInTwoCategories.bicategoryUnitHomMap")
Kerodon Construction 6.1.2.1（[Tag 02CQ](https://kerodon.net/tag/02CQ)）。対応表の状態：一部。

bicategoryUnitHomMapは任意の単位型ηによる原文のright adjunctそのものを直接構成する。homEquiv₂は随伴を仮定するので、任意のεだけによるleft adjunct全体までは数えない。

:::

:::proposition "kerodon_6_1_2_5" (lean := "CategoryTheory.Bicategory.Adjunction.homEquiv₁, CategoryTheory.Bicategory.Adjunction.homEquiv₂")
Kerodon Proposition 6.1.2.5（[Tag 02CU](https://kerodon.net/tag/02CU)）。対応表の状態：一部。

(η,ε)が両三角恒等式を満たすAdjunctionに強めればhomEquiv₂のleft\_inv/right\_invから同じadjunctの二つの含意を直接得る。片方の三角式だけの各主張には一般化しない。

:::

:::corollary "kerodon_6_1_2_6" (lean := "SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjunctionsInTwoCategories.BicategoryHomCorrespondence.adjunctionEquiv, CategoryTheory.Bicategory.Adjunction.homEquiv₂")
Kerodon Corollary 6.1.2.6（[Tag 02CV](https://kerodon.net/tag/02CV)）。対応表の状態：一部。

AdjunctionのhomEquiv₂は原文(1)から、同じunit/counitによるleft/right adjunctが互いに逆という(2)を直接返す。任意の指定η,εについての逆方向は含まない。

:::

:::corollary "kerodon_6_1_2_8" (lean := "CategoryTheory.Bicategory.rightZigzag_idempotent_of_left_triangle")
Kerodon Corollary 6.1.2.8（[Tag 02CX](https://kerodon.net/tag/02CX)）。対応表の状態：Mathlib にある。

仮定：双圏の η,ε と f 側の三角恒等式（Kerodon と一致）。結論：単位子を挿入した右 zigzag の合成が冪等。片側逆があれば消去により恒等（一致）。

:::

:::proposition "kerodon_6_1_2_9" (lean := "SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjunctionsInTwoCategories.bicategory_exists_adjunction_unit_iff, SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjunctionsInTwoCategories.bicategoryAdjunctionOfUnitHomBijective")
Kerodon Proposition 6.1.2.9（[Tag 02CY](https://kerodon.net/tag/02CY)）。対応表の状態：本体にある。

仮定：双圏の f,g と単位型の 2 射 η（Kerodon と一致）。結論：η を単位に持つ Adjunction の存在と、全ての T と c,d に対する右 adjunct 写像の全単射が同値（一致）。

:::

:::definition "kerodon_6_1_2_10" (lean := "SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjunctionsInTwoCategories.bicategory_exists_adjunction_unit_iff")
Kerodon Definition 6.1.2.10（[Tag 02CZ](https://kerodon.net/tag/02CZ)）。対応表の状態：本体にある。

仮定：双圏の f,g と指定 η:id→g∘f（Kerodon と一致）。結論：指定 η に対してある Adjunction a が存在して a.unit=η。原文の余単位の存在と三角恒等式を束ねた形（一致）。

:::

:::definition "kerodon_6_1_2_11"
Kerodon Variant 6.1.2.11（[Tag 02D0](https://kerodon.net/tag/02D0)）。対応表の状態：なし。

一般双圏のUnitHomCriterionは全試験対象Tの全Hom関手上の全単射を要求する。原文の通常圏で指定ηの各対象のHomだけによる判定・指定単位の比較・余単位の一意性の型ではない。StructuredArrowからの左随伴も指定ηとの比較を欠く。

宣言：`CategoryTheory.leftAdjointOfStructuredArrowInitials`、`SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjunctionsInTwoCategories.bicategory_exists_adjunction_unit_iff`

:::

:::definition "kerodon_6_1_2_12" (lean := "CategoryTheory.Bicategory.Adjunction.homEquiv₁")
Kerodon Variant 6.1.2.12（[Tag 02D1](https://kerodon.net/tag/02D1)）。対応表の状態：一部。

随伴のhomEquiv₁の逆は原文の指定ηを使った前合成側のHom全単射そのもの。(ηがunit)⇒判定の向きを直接与え、逆は含まない。

:::

:::proposition "kerodon_6_1_2_13" (lean := "CategoryTheory.Bicategory.Adjunction.homEquiv₁")
Kerodon Proposition 6.1.2.13（[Tag 02D2](https://kerodon.net/tag/02D2)）。対応表の状態：一部。

随伴を与えるとhomEquiv₁は原文(3)⇒(2)の指定εによるHom全単射を直接与える。任意εからunitを回収する逆・一意性は含まない。

:::

:::definition "kerodon_6_1_2_14" (lean := "CategoryTheory.Bicategory.Adjunction")
Kerodon Definition 6.1.2.14（[Tag 02D3](https://kerodon.net/tag/02D3)）。対応表の状態：Mathlib にある。

Bicategory.Adjunctionはunit・counitと二つの三角恒等式を持つ。∃a:Adjunction f g,a.counit=εと置けば、指定εに対するunitの存在という原文の定義をそのまま表す。専用述語名の不足をpartial理由にしない。

:::

# 6.1.3 Uniqueness of Adjoints

%%%
number := false
tag := "kerodon-6-1-3"
%%%

Kerodon [Tag 02D4](https://kerodon.net/tag/02D4)

:::proposition "kerodon_6_1_3_1" (lean := "CategoryTheory.Bicategory.Adjunction.homEquiv₂, CategoryTheory.Bicategory.Adjunction.homEquiv₁")
Kerodon Proposition 6.1.3.1（[Tag 02D5](https://kerodon.net/tag/02D5)）。対応表の状態：Mathlib にある。

仮定：双圏で η が随伴の単位（Lean が弱い：試験 1 射は恒等に限らない）。結論：homEquiv₂ の c=id と homEquiv₁ の g=id を用い、左随伴側および右随伴側の 2 射から単位型への全単射（一致）。

:::

:::definition "kerodon_6_1_3_2" (lean := "CategoryTheory.Bicategory.Adjunction.homEquiv₁, CategoryTheory.Bicategory.Adjunction.homEquiv₂")
Kerodon Variant 6.1.3.2（[Tag 02D6](https://kerodon.net/tag/02D6)）。対応表の状態：Mathlib にある。

仮定：双圏で ε が随伴の余単位（Lean が弱い：試験 1 射は恒等に限らない）。結論：homEquiv₁ と homEquiv₂ の試験 1 射を恒等に取り、両側から余単位型への全単射（一致）。

:::

:::corollary "kerodon_6_1_3_3" (lean := "CategoryTheory.Bicategory.Adjunction.homEquiv₁, CategoryTheory.Adjunction.rightAdjointUniq, SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction.rightAdjointIso") (uses := "kerodon_6_1_3_1")
Kerodon Corollary 6.1.3.3（[Tag 02D7](https://kerodon.net/tag/02D7)）。対応表の状態：一部。

homEquiv₁に適切な恒等1射を代入すれば、指定η′をunit経由に因子化するβの存在・一意性を直接得る。βの可逆性とη′がunitとなることの一般iffとε′側の全体は含まない。

:::

:::proposition "kerodon_6_1_3_4" (lean := "CategoryTheory.Bicategory.mateEquiv, CategoryTheory.Bicategory.conjugateEquiv")
Kerodon Proposition 6.1.3.4（[Tag 02D8](https://kerodon.net/tag/02D8)）。対応表の状態：Mathlib にある。

仮定：双圏における平行な二つの随伴 f⊣g、f′⊣g′（Kerodon と一致）。結論：conjugateEquiv で f→f′ と g′→g の 2 射を全単射で対応させる。単位・余単位との可換式は mate の条件の恒等脚の場合（一致）。

:::

:::definition "kerodon_6_1_3_5" (lean := "CategoryTheory.Bicategory.IsLeftAdjoint") (uses := "kerodon_6_1_3_3, kerodon_6_1_3_4")
Kerodon Notation 6.1.3.5（[Tag 02D9](https://kerodon.net/tag/02D9)）。対応表の状態：一部。

IsLeftAdjointは原文のLHomを張る1射の条件（右随伴が存在）そのもの。選んだ右随伴を反変な関手にする構成は含まない。

:::

:::corollary "kerodon_6_1_3_7" (lean := "CategoryTheory.Bicategory.Adjunction.homEquiv₂, CategoryTheory.Adjunction.leftAdjointUniq, SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction.leftAdjointIso") (uses := "kerodon_6_1_3_3")
Kerodon Corollary 6.1.3.7（[Tag 02DB](https://kerodon.net/tag/02DB)）。対応表の状態：一部。

homEquiv₂を恒等1射で特殊化すれば、指定η′のunitを経由するβによる因子化の存在・一意性を直接得る。可逆性のiffとε′側の全体は含まない。

:::

:::definition "kerodon_6_1_3_8" (lean := "CategoryTheory.Bicategory.IsRightAdjoint") (uses := "kerodon_6_1_3_5, kerodon_6_1_3_7")
Kerodon Notation 6.1.3.8（[Tag 02DC](https://kerodon.net/tag/02DC)）。対応表の状態：一部。

IsRightAdjointは原文のRHomを張る1射の条件そのもの。LHomの反対への圏同値と準逆は含まない。

:::

# 6.1.4 Adjoints of Isomorphisms

%%%
number := false
tag := "kerodon-6-1-4"
%%%

Kerodon [Tag 02DD](https://kerodon.net/tag/02DD)

:::proposition "kerodon_6_1_4_1"
Kerodon Proposition 6.1.4.1（[Tag 02DE](https://kerodon.net/tag/02DE)）。対応表の状態：なし。

e.adjは指定同値の標準unitの随伴、adjointifyCounitはunitとcounit両方の同型からの修正。原文の片方の1射が同値のとき任意の指定ηがunit iff ηが同型、という判定ではない。

宣言：`CategoryTheory.Bicategory.Equivalence.adj`、`CategoryTheory.Bicategory.adjointifyCounit`

:::

:::corollary "kerodon_6_1_4_2" (lean := "CategoryTheory.Bicategory.Equivalence.mkOfAdjointifyCounit, CategoryTheory.Bicategory.Equivalence.adj")
Kerodon Corollary 6.1.4.2（[Tag 02DF](https://kerodon.net/tag/02DF)）。対応表の状態：Mathlib にある。

仮定：双圏の f,g と両合成の恒等への同型（Kerodon と一致）。結論：mkOfAdjointifyCounit は同じ f,g で双圏同値を作り adj は f⊣g を与える。逆向きは逆双圏同値に適用（一致）。

:::

:::corollary "kerodon_6_1_4_4" (lean := "CategoryTheory.Adjunction.toEquivalence")
Kerodon Corollary 6.1.4.4（[Tag 02DH](https://kerodon.net/tag/02DH)）。対応表の状態：一部。

通常圏の双圏に制限するとAdjunction.toEquivalenceはunit/counitの成分同型から同じF,Gを逆関手とする圏同値を直接作り、原文(3)⇒(1),(2)を与える。一般双圏の三条件のiffは含まない。

:::

:::proposition "kerodon_6_1_4_6" (uses := "kerodon_6_1_1_1, kerodon_6_1_2_8")
Kerodon Proposition 6.1.4.6（[Tag 02DK](https://kerodon.net/tag/02DK)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：指定 η の左右 whiskering が同型で、g による各 Hom の後合成が充満忠実なら η が可逆な余単位を持つ随伴の単位となる判定。BicategoryHomCorrespondence.ofUnit は最初から指定した Hom 全単射を仮定。

:::

:::proposition "kerodon_6_1_4_7" (lean := "SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjunctionsInTwoCategories.bicategory_whiskerLeft_unit_isIso_of_counit, SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjunctionsInTwoCategories.bicategory_whiskerRight_unit_isIso_of_counit, CategoryTheory.Adjunction.whiskerLeft_unit_iso_of_R_fully_faithful")
Kerodon Proposition 6.1.4.7（[Tag 02DL](https://kerodon.net/tag/02DL)）。対応表の状態：一部。

bicategory\_whiskerLeft\_unit\_isIso\_of\_counitとwhiskerRight版は原文(1)から(2)の二つのwhiskerの可逆性を同じηについて直接返す。本質的全射の部分と他のiffは含まない。

:::

# 6.1.5 Composition of Adjunctions

%%%
number := false
tag := "kerodon-6-1-5"
%%%

Kerodon [Tag 02DM](https://kerodon.net/tag/02DM)

:::definition "kerodon_6_1_5_1" (lean := "CategoryTheory.Bicategory.Adjunction.compUnit")
Kerodon Construction 6.1.5.1（[Tag 02DN](https://kerodon.net/tag/02DN)）。対応表の状態：一部。

η,η′を指定随伴のunitに強めればcompUnitは原文と同じwhiskeringと結合子による合成unitを構成する。任意のunit型2射だけの構成は含まない。

:::

:::proposition "kerodon_6_1_5_3" (lean := "CategoryTheory.Adjunction.comp_homEquiv")
Kerodon Proposition 6.1.5.3（[Tag 02DQ](https://kerodon.net/tag/02DQ)）。対応表の状態：一部。

双圏をCat、試験圏Tを一点、η,η′を随伴のunitに限るとAdjunction.comp\_homEquivは原文の同じ二段のadjunctと合成adjunctの一致を直接返す。任意双圏と任意ηの可換四角には及ばない。

:::

:::corollary "kerodon_6_1_5_4" (lean := "CategoryTheory.Bicategory.Adjunction.comp")
Kerodon Corollary 6.1.5.4（[Tag 02DS](https://kerodon.net/tag/02DS)）。対応表の状態：Mathlib にある。

仮定：二つの指定 2 射 η,η′ がそれぞれ随伴の単位（Kerodon と一致）。結論：Bicategory.Adjunction.comp の単位が compUnit による合成 c(η,η′)（一致）。

:::

:::corollary "kerodon_6_1_5_5" (lean := "CategoryTheory.Bicategory.Adjunction.comp")
Kerodon Corollary 6.1.5.5（[Tag 02DT](https://kerodon.net/tag/02DT)）。対応表の状態：Mathlib にある。

仮定：双圏の合成可能な二つの随伴 f⊣g、f′⊣g′（Kerodon と一致）。結論：順に合成した左随伴 f′∘f と逆順に合成した右随伴 g∘g′ の Adjunction（一致）。

:::

:::corollary "kerodon_6_1_5_6" (lean := "CategoryTheory.Bicategory.Adjunction.comp")
Kerodon Corollary 6.1.5.6（[Tag 02DU](https://kerodon.net/tag/02DU)）。対応表の状態：Mathlib にある。

Bicategory.Adjunction.compは二つの随伴の合成を直接作る。存在する左右随伴の証人を取り合成すれば原文の二つの存在結論をともに得る。IsLeftAdjointの名の合成補題がなくても主張全体が直接従う。

:::

:::definition "kerodon_6_1_5_7" (lean := "CategoryTheory.Bicategory.Adjunction.compCounit")
Kerodon Construction 6.1.5.7（[Tag 02DV](https://kerodon.net/tag/02DV)）。対応表の状態：一部。

ε,ε′を指定随伴のcounitに強めればcompCounitは原文と同じwhiskering・結合子による合成counitを直接構成する。

:::

:::corollary "kerodon_6_1_5_9" (lean := "CategoryTheory.Bicategory.Adjunction.comp")
Kerodon Corollary 6.1.5.9（[Tag 02DX](https://kerodon.net/tag/02DX)）。対応表の状態：Mathlib にある。

仮定：双圏の合成可能な二つの随伴 (η,ε)、(η′,ε′)（Kerodon と一致）。結論：Adjunction.comp は単位 compUnit、余単位 compCounit を持つ合成の随伴（一致）。

:::

# 6.1.6 Duality in Monoidal Categories

%%%
number := false
tag := "kerodon-6-1-6"
%%%

Kerodon [Tag 02DY](https://kerodon.net/tag/02DY)

:::definition "kerodon_6_1_6_1" (lean := "CategoryTheory.ExactPairing")
Kerodon Definition 6.1.6.1（[Tag 02DZ](https://kerodon.net/tag/02DZ)）。対応表の状態：Mathlib にある。

仮定：モノイダル圏 C と二対象 X,Y（Kerodon と一致）。結論：ExactPairing Y X は 𝟙→Y⊗X と X⊗Y→𝟙 と二つの三角恒等式。Lean では引数順を Y,X とする（一致）。

:::

:::proposition "kerodon_6_1_6_5" (lean := "CategoryTheory.tensorLeftHomEquiv")
Kerodon Proposition 6.1.6.5（[Tag 02E3](https://kerodon.net/tag/02E3)）。対応表の状態：一部。

評価evが指定ExactPairing Y Xの評価であれば、tensorLeftHomEquivの逆は原文第一条件の同じevによる全単射を直接返す。duality datum⇒第一条件の向きで、任意evからの逆判定は含まない。

:::

:::definition "kerodon_6_1_6_6" (lean := "CategoryTheory.ExactPairing")
Kerodon Definition 6.1.6.6（[Tag 02E4](https://kerodon.net/tag/02E4)）。対応表の状態：Mathlib にある。

ExactPairing Y Xはcoev:1→Y⊗X、ev:X⊗Y→1と二つのzigzag等式を持つ。∃p:ExactPairing Y X,p.evaluation′=evという存在命題は原文の指定evがduality datumという定義そのもの。専用名は要らない。

:::

:::definition "kerodon_6_1_6_7" (lean := "CategoryTheory.tensorRightHomEquiv")
Kerodon Variant 6.1.6.7（[Tag 02E5](https://kerodon.net/tag/02E5)）。対応表の状態：一部。

指定coevを持つExactPairing Y Xを仮定するとtensorRightHomEquivは原文第二条件の同じcoevによる全単射を直接与える。任意coevから評価を回収する逆と一意性は含まない。

:::

:::definition "kerodon_6_1_6_8" (lean := "CategoryTheory.ExactPairing")
Kerodon Definition 6.1.6.8（[Tag 02E6](https://kerodon.net/tag/02E6)）。対応表の状態：Mathlib にある。

∃p:ExactPairing Y X,p.coevaluation′=coevは指定coevと組になるevおよび二つのzigzag等式の存在で、原文の定義全体をそのまま表す。

:::

:::definition "kerodon_6_1_6_9" (lean := "CategoryTheory.HasRightDual, CategoryTheory.HasLeftDual")
Kerodon Definition 6.1.6.9（[Tag 02E7](https://kerodon.net/tag/02E7)）。対応表の状態：Mathlib にある。

仮定：モノイダル圏 C と対象 X（Kerodon と一致）。結論：相方と ExactPairing を選ぶ HasLeftDual と HasRightDual。原文の ev:X⊗Y→𝟙 を与える X の右双対は Lean の HasLeftDual X（一致）。

:::

:::definition "kerodon_6_1_6_13" (lean := "CategoryTheory.tensorRightHomEquiv")
Kerodon Definition 6.1.6.13（[Tag 02EB](https://kerodon.net/tag/02EB)）。対応表の状態：一部。

評価evをExactPairing Y Xの評価に強めるとtensorRightHomEquiv Z Y X 1の逆と単位子が、原文後半の弱left dualの全単射Hom(Z,X)→Hom(Z⊗Y,1)を直接返す。任意evとweak right側は含まない。

:::

:::proposition "kerodon_6_1_6_15" (lean := "CategoryTheory.rightDualIso, CategoryTheory.tensorLeftHomEquiv")
Kerodon Proposition 6.1.6.15（[Tag 02ED](https://kerodon.net/tag/02ED)）。対応表の状態：一部。

tensorLeftHomEquivを終域1に特殊化すると、同じevによるduality datumからweak right dualの全単射が直接得られる。原文(1)の順方向のみで、任意指定evに関する逆は含まない。

:::

