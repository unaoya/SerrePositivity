import Verso
import VersoManual
import VersoBlueprint
import Mathlib.Order.Extension.Well
import Mathlib.Order.Hom.Set
import Mathlib.Order.InitialSeg
import Mathlib.Order.RelClasses
import Mathlib.Order.WellFounded
import Mathlib.SetTheory.Cardinal.Defs
import Mathlib.SetTheory.Cardinal.HasCardinalLT
import Mathlib.SetTheory.Cardinal.Order
import Mathlib.SetTheory.Cardinal.Regular
import Mathlib.SetTheory.Ordinal.Basic
import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.SmallSimplicialShapes

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "4.9 Size Conditions on ∞-Categories" =>
%%%
number := false
tag := "kerodon-4-9"
%%%

Kerodon の 4.9 節（[Tag 03PP](https://kerodon.net/tag/03PP)）の項目と、SerrePositivity・Mathlib の宣言との対応。本文は対応表（research/kerodon-coverage）の判定の理由の要約で、Kerodon の本文の写しではない。

# 4.9.1 Ordinals and Well-Orderings

%%%
number := false
tag := "kerodon-4-9-1"
%%%

Kerodon [Tag 03PV](https://kerodon.net/tag/03PV)

:::definition "kerodon_4_9_1_1" (lean := "WellFounded.has_min, WellFoundedLT, WellFounded.wellFounded_iff_has_min")
Kerodon Definition 4.9.1.1（[Tag 034C](https://kerodon.net/tag/034C)）。対応表の状態：Mathlib にある。

仮定：半順序上の狭義順序（Lean が弱い：has\_min と逆向きの定理は任意の関係）。結論：WellFoundedLT は \< の整礎性。空でない部分集合に極小元があることと同値（一致）。

:::

:::definition "kerodon_4_9_1_6" (lean := "IsWellOrder")
Kerodon Definition 4.9.1.6（[Tag 03Q0](https://kerodon.net/tag/03Q0)）。対応表の状態：Mathlib にある。

仮定：線形順序 S（Lean は順序関係 r を引数とする）（Kerodon と一致）。結論：IsWellOrder S (\<) は線形性の関係条件と整礎性。線形順序の極小元は最小元（一致）。

:::

:::definition "kerodon_4_9_1_7" (lean := "Ordinal, Ordinal.type")
Kerodon Definition 4.9.1.7（[Tag 03Q1](https://kerodon.net/tag/03Q1)）。対応表の状態：Mathlib にある。

仮定：固定宇宙の整列関係 r（Kerodon と一致）。結論：Ordinal は整列関係の順序同型類、Ordinal.type r はその順序型（一致）。

:::

:::definition "kerodon_4_9_1_8"
Kerodon Notation 4.9.1.8（[Tag 03Q2](https://kerodon.net/tag/03Q2)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：通常の順序数と表記・別表記・双対を照合。順序数に小文字ギリシャ文字を使う原文の表記規約。Ordinal は型で文字の選び方を宣言しない。

:::

:::definition "kerodon_4_9_1_11" (lean := "InitialSeg")
Kerodon Definition 4.9.1.11（[Tag 03Q5](https://kerodon.net/tag/03Q5)）。対応表の状態：Mathlib にある。

仮定：二つの線形順序（Lean が弱い：InitialSeg は一般の関係に定義）。結論：順序埋め込みで、像の任意の点より小さい点が再び像にある（一致）。

:::

:::proposition "kerodon_4_9_1_14"
Kerodon Proposition 4.9.1.14（[Tag 03Q8](https://kerodon.net/tag/03Q8)）。対応表の状態：なし。

InitialSeg.le\_apply\_iffは一つの始切片埋め込みの下方閉性。原文の別の任意の狭義単調f′との点ごとの比較f(s)≤f′(s)ではなく、その証明部品。

宣言：`InitialSeg.le_apply_iff`

:::

:::corollary "kerodon_4_9_1_15" (lean := "InitialSeg.subsingleton_of_trichotomous_of_irrefl")
Kerodon Corollary 4.9.1.15（[Tag 03Q9](https://kerodon.net/tag/03Q9)）。対応表の状態：Mathlib にある。

仮定：始域が整列順序、標的が線形順序（Lean が弱い：始域は WellFounded、標的は三分律と非反射性で足りる）。結論：InitialSeg の型は Subsingleton なので二つの始切片埋め込みは等しい（一致）。

:::

:::corollary "kerodon_4_9_1_16" (lean := "OrderIso.subsingleton_of_wellFoundedLT")
Kerodon Corollary 4.9.1.16（[Tag 03QA](https://kerodon.net/tag/03QA)）。対応表の状態：Mathlib にある。

仮定：始域と標的が整列順序（Lean が弱い：標的は前順序で足りる）。結論：OrderIso S T は Subsingleton（一致）。

:::

:::corollary "kerodon_4_9_1_17" (lean := "InitialSeg.total")
Kerodon Corollary 4.9.1.17（[Tag 03QB](https://kerodon.net/tag/03QB)）。対応表の状態：Mathlib にある。

仮定：二つの整列関係 r,s（Kerodon と一致）。結論：InitialSeg r s ⊕ InitialSeg s r を得る（一致）。

:::

:::definition "kerodon_4_9_1_19" (lean := "Ordinal.partialOrder, Ordinal.type_le_iff")
Kerodon Definition 4.9.1.19（[Tag 03QD](https://kerodon.net/tag/03QD)）。対応表の状態：Mathlib にある。

仮定：α,β が整列関係 r,s の順序型（Kerodon と一致）。結論：Ordinal.type r ≤ Ordinal.type s と InitialSeg r s の存在が同値（一致）。

:::

:::proposition "kerodon_4_9_1_20" (lean := "Ordinal.lt_wf")
Kerodon Proposition 4.9.1.20（[Tag 03QE](https://kerodon.net/tag/03QE)）。対応表の状態：Mathlib にある。

仮定：固定宇宙の順序数（Kerodon と一致）。結論：順序数の ≤ を含む LinearOrder instance（一致）。

:::

:::proposition "kerodon_4_9_1_22" (lean := "Ordinal.enum, Ordinal.typein")
Kerodon Proposition 4.9.1.22（[Tag 03QG](https://kerodon.net/tag/03QG)）。対応表の状態：Mathlib にある。

仮定：整列関係 r と α=Ordinal.type r（Kerodon と一致）。結論：enum は Iio α→S の順序同型。逆向きが typein で、各 s を s より小さい部分の順序型に写す（一致）。

:::

:::corollary "kerodon_4_9_1_23" (lean := "Ordinal.type_lt_Iio, Ordinal.ToType.mk")
Kerodon Corollary 4.9.1.23（[Tag 03QH](https://kerodon.net/tag/03QH)）。対応表の状態：Mathlib にある。

仮定：任意の順序数 α（Kerodon と一致）。結論：α 未満の順序数の順序型は宇宙持ち上げをした α（一致）。

:::

:::corollary "kerodon_4_9_1_24" (lean := "Ordinal.lt_wf, WellFounded.has_min")
Kerodon Corollary 4.9.1.24（[Tag 03QJ](https://kerodon.net/tag/03QJ)）。対応表の状態：Mathlib にある。

仮定：固定宇宙の順序数の空でない部分集合（Kerodon と一致）。結論：Ordinal.lt\_wf と WellFounded.has\_min により極小元が存在。線形性により最小（一致）。

:::

:::definition "kerodon_4_9_1_26"
Kerodon Definition 4.9.1.26（[Tag 03QL](https://kerodon.net/tag/03QL)）。対応表の状態：一部。

Order.IsCofinal(range f)は原文の∀t∃s,t≤f(s)という非有界性の成分そのもの。単調性を含む写像の共終性の全定義は含まない。

宣言：`IsCofinal`

:::

:::proposition "kerodon_4_9_1_27"
Kerodon Proposition 4.9.1.27（[Tag 03QM](https://kerodon.net/tag/03QM)）。対応表の状態：一部。

T自身も整列順序と仮定すれば、exists\_cof\_eqの共終部分集合は誘導順序でも整列し、包含は単調なので原文と同じ存在結論を直接得る。任意の線形順序Tではない。

宣言：`Order.exists_cof_eq`、`Order.ord_cof_eq_type_lt`、`isCofinal_setOfPred_imp_lt`

:::

:::definition "kerodon_4_9_1_28"
Kerodon Definition 4.9.1.28（[Tag 03QN](https://kerodon.net/tag/03QN)）。対応表の状態：なし。

Order.cof/Ordinal.cofは共終部分集合の最小基数。原文の整列順序からの共終写像の最小順序型との同定を型に持たず、基数値を取るというだけでは同じ定義のcomponentではない。

宣言：`Order.cof`、`Ordinal.cof`

:::

:::proposition "kerodon_4_9_1_33"
Kerodon Proposition 4.9.1.33（[Tag 03QT](https://kerodon.net/tag/03QT)）。対応表の状態：なし。

cof\_le/le\_cof\_iffは像集合の基数による下界。原文は非単調な非有界写像の始域の順序型の最小性で、基数の不等式を順序数の最小性に移す比較が必要。

宣言：`Order.cof_le`、`Order.le_cof_iff`

:::

:::theorem "kerodon_4_9_1_34" (lean := "WellOrderingRel.isWellOrder, exists_wellFoundedLT")
Kerodon Theorem 4.9.1.34（[Tag 03QU](https://kerodon.net/tag/03QU)）。対応表の状態：Mathlib にある。

仮定：任意の型 S（Kerodon と一致）。結論：WellOrderingRel が整列関係であり、整礎な \< を持つ線形順序の存在を与える（一致）。

:::

:::proposition "kerodon_4_9_1_35" (lean := "WellFounded.wellOrderExtension")
Kerodon Proposition 4.9.1.35（[Tag 03QV](https://kerodon.net/tag/03QV)）。対応表の状態：Mathlib にある。

仮定：整礎な半順序（Lean が弱い：wellOrderExtension は整礎な関係から構成）。結論：整礎な関係を狭義部分に含む線形順序。半順序では ≤ も延長（一致）。

:::

# 4.9.2 Cardinals and Cardinality

%%%
number := false
tag := "kerodon-4-9-2"
%%%

Kerodon [Tag 03QW](https://kerodon.net/tag/03QW)

:::definition "kerodon_4_9_2_1" (lean := "Cardinal, Cardinal.ord")
Kerodon Definition 4.9.2.1（[Tag 03QX](https://kerodon.net/tag/03QX)）。対応表の状態：Mathlib にある。

仮定：固定宇宙の集合（Kerodon と一致）。結論：Cardinal は全単射による商、Cardinal.ord は同じ濃度の最小順序数を与える（一致）。

:::

:::proposition "kerodon_4_9_2_3" (lean := "Cardinal.le_def")
Kerodon Proposition 4.9.2.3（[Tag 03QZ](https://kerodon.net/tag/03QZ)）。対応表の状態：Mathlib にある。

仮定：同一宇宙の型 S,T（Kerodon と一致）。結論：Cardinal.mk S ≤ Cardinal.mk T と単射 S↪T の存在が同値（一致）。

:::

:::corollary "kerodon_4_9_2_4" (lean := "Cardinal.eq")
Kerodon Corollary 4.9.2.4（[Tag 03R0](https://kerodon.net/tag/03R0)）。対応表の状態：Mathlib にある。

仮定：同一宇宙の型 S,T（Kerodon と一致）。結論：Cardinal.mk S = Cardinal.mk T と Equiv S T の存在が同値（一致）。

:::

:::corollary "kerodon_4_9_2_5" (lean := "Cardinal.ord_le, Cardinal.ord_card_le")
Kerodon Corollary 4.9.2.5（[Tag 03R1](https://kerodon.net/tag/03R1)）。対応表の状態：Mathlib にある。

仮定：整列集合の順序型 α（Lean が弱い：α は任意の順序数）。結論：c.ord≤α と c≤α.card が同値、かつ α.card.ord≤α。従って α.card.ord が最大（一致）。

:::

:::proposition "kerodon_4_9_2_8" (lean := "Cardinal.cantor")
Kerodon Proposition 4.9.2.8（[Tag 03R4](https://kerodon.net/tag/03R4)）。対応表の状態：Mathlib にある。

仮定：任意の集合 S（Lean はその濃度 a を引数に取る）（Kerodon と一致）。結論：a\<2\^a。2\^a は S の冪集合の濃度（一致）。

:::

:::proposition "kerodon_4_9_2_15"
Kerodon Proposition 4.9.2.15（[Tag 03RA](https://kerodon.net/tag/03RA)）。対応表の状態：なし。

Cardinal値のOrder.cofを定義することは、原文のOrdinal値の最小順序型が始順序数であることの証明ではない。exists\_ord\_cof\_eqも整列Tの共終部分集合の型で、原文の最小性との比較を欠く。

宣言：`Order.cof`、`Ordinal.exists_ord_cof_eq`

:::

# 4.9.3 Small Sets

%%%
number := false
tag := "kerodon-4-9-3"
%%%

Kerodon [Tag 03RB](https://kerodon.net/tag/03RB)

:::definition "kerodon_4_9_3_1" (lean := "HasCardinalLT")
Kerodon Definition 4.9.3.1（[Tag 03RC](https://kerodon.net/tag/03RC)）。対応表の状態：Mathlib にある。

仮定：基数 κ と集合 S（Kerodon と一致）。結論：HasCardinalLT S κ は S の濃度が κ 未満であること（一致）。

:::

:::proposition "kerodon_4_9_3_5" (uses := "kerodon_4_9_2_5")
Kerodon Proposition 4.9.3.5（[Tag 03RG](https://kerodon.net/tag/03RG)）。対応表の状態：一部。

Cardinal.mul\_lt\_of\_ltは二つのκ-small集合の積の濃度がκ未満と直接返す。一般の無限κでよいが、任意有限個の積の一括した閉性は含まない。

宣言：`Cardinal.mul_lt_of_lt`

:::

:::corollary "kerodon_4_9_3_6" (uses := "kerodon_4_9_3_5")
Kerodon Corollary 4.9.3.6（[Tag 03RH](https://kerodon.net/tag/03RH)）。対応表の状態：一部。

Cardinal.add\_lt\_of\_ltは二つのκ-small集合の余積の濃度がκ未満と直接返す。任意有限個の余積の一括した閉性は含まない。

宣言：`Cardinal.add_lt_of_lt`

:::

:::proposition "kerodon_4_9_3_7"
Kerodon Proposition 4.9.3.7（[Tag 03RJ](https://kerodon.net/tag/03RJ)）。対応表の状態：一部。

λが正則の場合、sum\_lt\_of\_isRegularは添字濃度\<λと各項\<λから同じ余積濃度\<λを直接返す。原文(1)⇒(2)のこの場合で、一般の特異λと逆向きは含まない。

宣言：`Cardinal.iSup_lt_of_isRegular`、`Cardinal.sum_lt_of_isRegular`、`Cardinal.iSup_lt_of_lt_cof_ord`

:::

:::corollary "kerodon_4_9_3_8"
Kerodon Corollary 4.9.3.8（[Tag 03RK](https://kerodon.net/tag/03RK)）。対応表の状態：なし。

sum\_lt\_of\_isRegularは正則λについての小さい余積の上界。原文の最小の失敗する添字κの存在・下限のいずれも型の結論ではない。

宣言：`Cardinal.sum_lt_of_isRegular`

:::

:::corollary "kerodon_4_9_3_9"
Kerodon Corollary 4.9.3.9（[Tag 03RL](https://kerodon.net/tag/03RL)）。対応表の状態：一部。

λも正則と仮定するとsum\_lt\_of\_isRegularは同じ添字族の余積がλ-smallという結論を直接返す。cf(λ)=λであるこの場合に限り、特異λは含まない。

宣言：`Cardinal.card_iUnion_lt_iff_forall_of_isRegular`、`Cardinal.sum_lt_of_isRegular`

:::

:::definition "kerodon_4_9_3_10" (lean := "Cardinal.IsRegular")
Kerodon Definition 4.9.3.10（[Tag 03RM](https://kerodon.net/tag/03RM)）。対応表の状態：Mathlib にある。

仮定：無限基数 κ（Lean は述語に無限性を含める）（Kerodon と一致）。結論：Cardinal.IsRegular は κ.ord.cof = κ に当たる条件。無限基数でこれを満たさないものが特異（一致）。

:::

:::definition "kerodon_4_9_3_16"
Kerodon Definition 4.9.3.16（[Tag 03RT](https://kerodon.net/tag/03RT)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：通常の cf と正則性・指数の評価・有界・共終を照合。非有界な濃度の積族の最小添字濃度としての ecf(λ)。通常の Cardinal.cof は順序の共終性を測る。

:::

:::proposition "kerodon_4_9_3_20"
Kerodon Proposition 4.9.3.20（[Tag 03S0](https://kerodon.net/tag/03S0)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：通常の cf と正則性・指数の評価・有界・共終を照合。ecf(λ) が正則であること。通常の Cardinal.cof の正則性は積の濃度を用いる ecf の正則性ではない。

:::

:::definition "kerodon_4_9_3_21"
Kerodon Definition 4.9.3.21（[Tag 03RW](https://kerodon.net/tag/03RW)）。対応表の状態：なし。

IsInaccessibleは正則かつ強極限と非可算性の定義。原文のκ-smallな全ての族の積への閉性と結ぶ型は引用にないので、同じ述語のcomponentとはしない。

宣言：`Cardinal.IsInaccessible`

:::

:::proposition "kerodon_4_9_3_22" (lean := "Cardinal.isInaccessible_def, Cardinal.IsStrongLimit")
Kerodon Proposition 4.9.3.22（[Tag 05YL](https://kerodon.net/tag/05YL)）。対応表の状態：Mathlib にある。

仮定：非可算基数 λ（Kerodon と一致）。結論：非可算性の下で IsInaccessible λ と IsRegular λ∧IsStrongLimit λ が同値。強極限は κ\<λ⇒2\^κ\<λ（一致）。

:::

# 4.9.4 Small Simplicial Sets

%%%
number := false
tag := "kerodon-4-9-4"
%%%

Kerodon [Tag 03S1](https://kerodon.net/tag/03S1)

:::definition "kerodon_4_9_4_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsKappaSmall")
Kerodon Definition 4.9.4.1（[Tag 03S2](https://kerodon.net/tag/03S2)）。対応表の状態：本体にある。

仮定：無限基数 κ と単体集合 X（Lean が弱い：IsKappaSmall は任意の基数で定義）。結論：X の全次数の非退化単体の集合の濃度が κ 未満（一致）。

:::

:::proposition "kerodon_4_9_4_10" (uses := "kerodon_1_1_0_6, kerodon_1_1_3_8, kerodon_3_6_1_7, kerodon_4_9_3_5, kerodon_4_9_3_6")
Kerodon Proposition 4.9.4.10（[Tag 03SA](https://kerodon.net/tag/03SA)）。対応表の状態：一部。

hasCardinalLT\_obj\_of\_NとhasCardinalLT\_N\_of\_objはκを非可算正則に強めると原文(1)⇔(2)の同じ非退化単体全体/各次数の濃度条件を直接結ぶ。有限KからのHomの条件(3)と一般の共終数仮定は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.hasCardinalLT_obj_of_N`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.hasCardinalLT_N_of_obj`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.hasCardinalLT_simplices_of_isKappaSmall`

:::

:::corollary "kerodon_4_9_4_12" (uses := "kerodon_1_1_0_6, kerodon_4_9_3_5, kerodon_4_9_4_10")
Kerodon Corollary 4.9.4.12（[Tag 03SC](https://kerodon.net/tag/03SC)）。対応表の状態：一部。

isKappaSmall\_prodはκを正則に強めると二項積の同じκ-small性を直接返す。任意の無限κと任意有限個への一般化は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.isKappaSmall_prod`

:::

:::corollary "kerodon_4_9_4_13" (uses := "kerodon_1_1_0_6, kerodon_4_9_3_5, kerodon_4_9_3_6, kerodon_4_9_4_10")
Kerodon Corollary 4.9.4.13（[Tag 05P7](https://kerodon.net/tag/05P7)）。対応表の状態：一部。

isKappaSmall\_joinはκを正則に強めると同じjoinのκ-small性を直接返す。任意の非正則な無限κは含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.isKappaSmall_join`

:::

:::corollary "kerodon_4_9_4_14" (uses := "kerodon_1_1_0_6, kerodon_4_9_4_10")
Kerodon Corollary 4.9.4.14（[Tag 03SD](https://kerodon.net/tag/03SD)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：有限単体・小さい単体数・指数と Ex∞・通常圏での小ささを照合。有限 K に対する Fun(K,S) が非可算 κ 未満の単体数を保つ評価。小さい圏や κ-presentable の型にこの指数対象の評価がない。

:::

:::corollary "kerodon_4_9_4_16" (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_3_3_6_1, kerodon_4_9_4_10")
Kerodon Corollary 4.9.4.16（[Tag 05P8](https://kerodon.net/tag/05P8)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：有限単体・小さい単体数・指数と Ex∞・通常圏での小ささを照合。Ex∞(S) の単体数が非可算 κ 未満であること。Ex∞ の Kan 性・弱同値性の型は濃度に言及しない。

:::

:::corollary "kerodon_4_9_4_18" (uses := "kerodon_1_1_0_6, kerodon_4_9_3_16, kerodon_4_9_4_10, kerodon_4_9_4_12")
Kerodon Corollary 4.9.4.18（[Tag 03SF](https://kerodon.net/tag/03SF)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：有限単体・小さい単体数・指数と Ex∞・通常圏での小ささを照合。ecf(λ) 未満の個数の積で λ-small な単体集合が閉じる評価。通常の κ-正則性による小図式の補題の濃度条件が異なる。

:::

:::corollary "kerodon_4_9_4_19" (uses := "kerodon_1_1_0_6, kerodon_4_9_4_14, kerodon_4_9_4_18")
Kerodon Corollary 4.9.4.19（[Tag 03SG](https://kerodon.net/tag/03SG)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：有限単体・小さい単体数・指数と Ex∞・通常圏での小ささを照合。ecf(λ) 未満の K に対する Fun(K,S) の λ-small 性。有限図式への制限や universe lift ではこの指数共終数条件がない。

:::

:::proposition "kerodon_4_9_4_20" (uses := "kerodon_1_1_0_6, kerodon_4_9_4_10")
Kerodon Proposition 4.9.4.20（[Tag 05YN](https://kerodon.net/tag/05YN)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：有限単体・小さい単体数・指数と Ex∞・通常圏での小ささを照合。κ⁺-small 単体集合の同型類全体の濃度を 2\^κ で抑える評価。一個の単体集合の universe lift と区別した。

:::

:::definition "kerodon_4_9_4_21" (uses := "kerodon_1_1_0_6, kerodon_1_1_4_12")
Kerodon Variant 4.9.4.21（[Tag 05YP](https://kerodon.net/tag/05YP)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：有限単体・小さい単体数・指数と Ex∞・通常圏での小ささを照合。次元 d 以下かつ非退化単体数 n の単体集合の同型類の有限性。個々の finite simplicial set の補題は同型類全体を数えない。

:::

# 4.9.5 Essential Smallness

%%%
number := false
tag := "kerodon-4-9-5"
%%%

Kerodon [Tag 03SH](https://kerodon.net/tag/03SH)

:::definition "kerodon_4_9_5_1"
Kerodon Definition 4.9.5.1（[Tag 03SJ](https://kerodon.net/tag/03SJ)）。対応表の状態：なし。

HasSmallKanModelは大小の宇宙間のKan模型の述語で、原文の指定の非可算基数κとκ-small性の評価を型に持たない。数値κへの比較なしに宇宙版の類似をspecialとしない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.HasSmallKanModel`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.hull`

:::

:::proposition "kerodon_4_9_5_4" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_4_5_2_12")
Kerodon Proposition 4.9.5.4（[Tag 06T4](https://kerodon.net/tag/06T4)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：通常圏の本質的小・圏同値と core・全部分複体・積・引き戻し・関手圏を照合。minimal ∞ 圏の κ-small 性と本質的 κ-small 性の同値。通常圏の本質像の小ささと異なり minimality が比較に必要。

:::

:::corollary "kerodon_4_9_5_5" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_4_5_2_15, kerodon_4_9_5_4")
Kerodon Corollary 4.9.5.5（[Tag 03TH](https://kerodon.net/tag/03TH)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：通常圏の本質的小・圏同値と core・全部分複体・積・引き戻し・関手圏を照合。各単体集合を本質的に小さくする最小非可算濃度の存在と後続性。universe による EssentiallySmall に最小濃度の添字がない。

:::

:::definition "kerodon_4_9_5_6"
Kerodon Variant 4.9.5.6（[Tag 03SM](https://kerodon.net/tag/03SM)）。対応表の状態：一部。

HasSmallKanModelは準圏Xが小さいKan模型と圏同値という条件。逆同値を取ればXから小さいKan準圏へのcategorical equivalenceを直接与え、原文の小さい比較先をKanに制限した場合。任意の小さい準圏の模型の条件は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.HasSmallKanModel`

:::

:::proposition "kerodon_4_9_5_7" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_4_1_3_2, kerodon_4_9_4_10")
Kerodon Proposition 4.9.5.7（[Tag 03SN](https://kerodon.net/tag/03SN)）。対応表の状態：なし。

Hullは与えたambient準圏の中の種を含む小さい準圏と因子化性で、Aからの射のinner anodyne性を場に持たない。原文の指定inner anodyneな小さい準圏置換を直接構成しない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.exists_hull_hasCardinalLT`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.hasCardinalLT_innerHornClosure`

:::

:::definition "kerodon_4_9_5_11"
Kerodon Variant 4.9.5.11（[Tag 03SS](https://kerodon.net/tag/03SS)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：通常圏の本質的小・圏同値と core・全部分複体・積・引き戻し・関手圏を照合。本質的 κ-small な ∞ 圏の族の非交和が添字数の条件下で本質的 κ-small。通常圏の Small の coproduct は単体数の κ 上限を述べない。

:::

:::proposition "kerodon_4_9_5_14" (uses := "kerodon_1_4_0_1, kerodon_4_5_3_33")
Kerodon Proposition 4.9.5.14（[Tag 03SU](https://kerodon.net/tag/03SU)）。対応表の状態：なし。

通常圏・宇宙のEssentiallySmallに関する結果で、原文の数値κの評価と準圏のreplete subcategoryに関する同じ結論への比較を欠く。

宣言：`CategoryTheory.ObjectProperty.EssentiallySmall.of_le`、`CategoryTheory.ObjectProperty.instEssentiallySmallFullSubcategoryOfLocallySmallOfEssentiallySmall_1`、`CategoryTheory.ObjectProperty.instEssentiallySmallTopOfEssentiallySmall`

:::

:::corollary "kerodon_4_9_5_15"
Kerodon Corollary 4.9.5.15（[Tag 03SV](https://kerodon.net/tag/03SV)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：通常圏の本質的小・圏同値と core・全部分複体・積・引き戻し・関手圏を照合。本質的 κ-small な C の core の本質的 κ-small 性。quasicategoryCore\_kanComplex は core の Kan 性だけを扱う。

:::

:::corollary "kerodon_4_9_5_16" (uses := "kerodon_1_4_0_1, kerodon_4_9_5_14")
Kerodon Corollary 4.9.5.16（[Tag 03SW](https://kerodon.net/tag/03SW)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：通常圏の本質的小・圏同値と core・全部分複体・積・引き戻し・関手圏を照合。本質的 κ-small な C の任意の充満部分 ∞ 圏の本質的 κ-small 性。通常圏の Small や頂点部分複体の κ 制約なしの型とは異なる。

:::

:::proposition "kerodon_4_9_5_17" (uses := "kerodon_1_4_0_1, kerodon_4_9_4_12, kerodon_4_9_4_14")
Kerodon Proposition 4.9.5.17（[Tag 03SX](https://kerodon.net/tag/03SX)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：通常圏の本質的小・圏同値と core・全部分複体・積・引き戻し・関手圏を照合。三つの本質的 κ-small な ∞ 圏から作る oriented fiber product の本質的 κ-small 性。厳密 pullback の通常の small 性では oriented product を評価しない。

:::

:::corollary "kerodon_4_9_5_18" (uses := "kerodon_1_4_0_1, kerodon_4_9_5_16, kerodon_4_9_5_17")
Kerodon Corollary 4.9.5.18（[Tag 03SY](https://kerodon.net/tag/03SY)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：通常圏の本質的小・圏同値と core・全部分複体・積・引き戻し・関手圏を照合。本質的 κ-small 性の homotopy fiber product での閉性。lax pullback の同値部分複体の比較には濃度の上限がない。

:::

:::corollary "kerodon_4_9_5_19" (uses := "kerodon_1_4_0_1, kerodon_4_9_5_18")
Kerodon Corollary 4.9.5.19（[Tag 03SZ](https://kerodon.net/tag/03SZ)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：通常圏の本質的小・圏同値と core・全部分複体・積・引き戻し・関手圏を照合。categorical pullback の四角での本質的 κ-small 性の伝播。既存の categorical pullback の判定は三隅の κ 制約を比較しない。

:::

:::corollary "kerodon_4_9_5_20"
Kerodon Corollary 4.9.5.20（[Tag 04J8](https://kerodon.net/tag/04J8)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：通常圏の本質的小・圏同値と core・全部分複体・積・引き戻し・関手圏を照合。ecf(λ) の制約を持つ K と本質的 λ-small な C から Fun(K,C) の本質的 λ-small 性。通常の functor category の Small の型はこの濃度条件を持たない。

:::

# 4.9.6 Small Kan Complexes

%%%
number := false
tag := "kerodon-4-9-6"
%%%

Kerodon [Tag 03TJ](https://kerodon.net/tag/03TJ)

:::proposition "kerodon_4_9_6_1" (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_3_1_3_3, kerodon_4_5_2_15, kerodon_4_9_3_5, kerodon_4_9_4_10, kerodon_4_9_5_4, kerodon_5_2_2_19")
Kerodon Proposition 4.9.6.1（[Tag 03TK](https://kerodon.net/tag/03TK)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：Kan の連結成分と π 群・有限・小さいモデル・ファイバーと基底変換を照合。非可算正則 κ における Kan 複体の本質的 κ-small 性を成分数と各 π 群の濃度で判定。π の補題や Small モデルは両条件を結ばない。

:::

:::corollary "kerodon_4_9_6_2" (uses := "kerodon_1_2_5_1, kerodon_3_2_6_2, kerodon_4_9_5_19, kerodon_4_9_6_1")
Kerodon Corollary 4.9.6.2（[Tag 03TL](https://kerodon.net/tag/03TL)）。対応表の状態：なし。

全空間の各次数のSmallから単体fiberのSmallという宇宙の主張。原文の指定κでの本質的小ささと各頂点fiberの本質的小ささのiffのいずれの向きも直接述べない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.hasSmallSimplexFibers_of_small_total`

:::

# 4.9.7 Local Smallness

%%%
number := false
tag := "kerodon-4-9-7"
%%%

Kerodon [Tag 03TN](https://kerodon.net/tag/03TN)

:::definition "kerodon_4_9_7_1"
Kerodon Definition 4.9.7.1（[Tag 03TP](https://kerodon.net/tag/03TP)）。対応表の状態：なし。

IsLocallySmallはu+1/uの宇宙差の述語。原文の指定κと各Homのessentiallyκ-smallの濃度条件を結ぶ型がなく、宇宙版の類似だけは数えない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsLocallySmall`

:::

:::definition "kerodon_4_9_7_6"
Kerodon Variant 4.9.7.6（[Tag 03TU](https://kerodon.net/tag/03TU)）。対応表の状態：一部。

IsLocallySmallはu+1の準圏Cの各頂点対にuのKan模型を与える。自然なpinched→interval比較の圏同値を合成し、Kan上でホモトピー同値へ移すと原文の各interval Homのessential smallnessを直接得る。この宇宙を指定した範囲だけ。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsLocallySmall`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace_isQCatEquivalence`、`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace_postOfEq`

:::

:::proposition "kerodon_4_9_7_7" (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_3_2_6_5, kerodon_4_4_5_4, kerodon_4_4_5_10, kerodon_4_5_2_15, kerodon_4_9_3_5, kerodon_4_9_4_10, kerodon_4_9_5_16, kerodon_4_9_5_19, kerodon_4_9_6_1, kerodon_4_9_6_2")
Kerodon Proposition 4.9.7.7（[Tag 03TW](https://kerodon.net/tag/03TW)）。対応表の状態：なし。

essentiallySmall\_iffは通常圏の宇宙版。原文の指定κの濃度条件・準圏のcoreのπ₀・関手∞圏の比較への型の対応がない。

宣言：`CategoryTheory.essentiallySmall_iff`

:::

:::corollary "kerodon_4_9_7_8"
Kerodon Corollary 4.9.7.8（[Tag 03UR](https://kerodon.net/tag/03UR)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：1 圏の局所小性・空間の局所小性・有限・正則基数の場合を照合。ecf(λ)≥κ のもとで Fun(C,D) の局所 λ-small 性を写像空間から評価。universe lift と本質的小の補題には ecf 条件がない。

:::

:::corollary "kerodon_4_9_7_9"
Kerodon Corollary 4.9.7.9（[Tag 03US](https://kerodon.net/tag/03US)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：1 圏の局所小性・空間の局所小性・有限・正則基数の場合を照合。本質的に小さい C と局所小な ∞ 圏 D による Fun(C,D) の局所小性。1 圏版の LocallySmall は Kan 写像空間の本質的小ささを意味しない。

:::

:::definition "kerodon_4_9_7_10"
Kerodon Variant 4.9.7.10（[Tag 04JA](https://kerodon.net/tag/04JA)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：1 圏の局所小性・空間の局所小性・有限・正則基数の場合を照合。κ-small な K と局所 λ-small な C から Fun(K,C) の局所 λ-small 性。局所小な通常圏の指数対象に単体数と λ の制約がない。

:::

# 4.9.8 Small Fibrations

%%%
number := false
tag := "kerodon-4-9-8"
%%%

Kerodon [Tag 047A](https://kerodon.net/tag/047A)

:::definition "kerodon_4_9_8_1" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1")
Kerodon Definition 4.9.8.1（[Tag 047B](https://kerodon.net/tag/047B)）。対応表の状態：なし。

HasEssentiallySmallFibersはleft fibrationの頂点fiberの宇宙版で、原文の指定κと全ての単体への引き戻しの本質的κ-small性・局所κ-small性を型に持たない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.HasEssentiallySmallFibers`

:::

:::definition "kerodon_4_9_8_2" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1")
Kerodon Variant 4.9.8.2（[Tag 047C](https://kerodon.net/tag/047C)）。対応表の状態：一部。

HasEssentiallySmallFibersはleft fibrationの各頂点fiberに小さいKan模型を直接要求する。原文のessentially smallの全単体条件のうちn=0の成分に限り、任意の高次単体・locally smallの条件は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.HasEssentiallySmallFibers`

:::

:::proposition "kerodon_4_9_8_7" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1")
Kerodon Proposition 4.9.8.7（[Tag 05PD](https://kerodon.net/tag/05PD)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：頂点と Δ¹ のファイバー・通常圏の局所小性と合成・濃度と正則性を照合。内ファイブレーションの本質的 κ-small 性を各辺 Δ¹ 上の引き戻し等で判定。個別の pullback の small 型にはこの局所判定がない。

:::

:::corollary "kerodon_4_9_8_8"
Kerodon Corollary 4.9.8.8（[Tag 047N](https://kerodon.net/tag/047N)）。対応表の状態：なし。

left fibrationの頂点fiberの宇宙版の基底変換であり、原文の指定κでの各辺全体のessential smallnessを直接返す型ではない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.HasEssentiallySmallFibers.pullback_snd`

:::

:::proposition "kerodon_4_9_8_10" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_4_9_5_4, kerodon_5_3_8_11")
Kerodon Proposition 4.9.8.10（[Tag 05PE](https://kerodon.net/tag/05PE)）。対応表の状態：なし。

total\_obj\_smallは各次数のSmallという宇宙の結論。原文の数値λ・cf(λ)と本質的λ-smallな準圏模型の存在を直接結論する型がない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.HasSmallSimplexFibers.total_obj_small`

:::

:::definition "kerodon_4_9_8_11" (uses := "kerodon_1_1_0_6, kerodon_1_4_0_1, kerodon_4_9_4_19, kerodon_4_9_8_10")
Kerodon Variant 4.9.8.11（[Tag 05PF](https://kerodon.net/tag/05PF)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：頂点と Δ¹ のファイバー・通常圏の局所小性と合成・濃度と正則性を照合。ecf(λ) を使った内ファイブレーションの本質的 λ-small 性の判定。通常の κ-正則性に基づく small 補題に指数共終数条件がない。

:::

:::corollary "kerodon_4_9_8_12" (uses := "kerodon_1_4_0_1, kerodon_4_5_2_15, kerodon_4_5_3_33, kerodon_4_9_5_4, kerodon_4_9_8_10")
Kerodon Corollary 4.9.8.12（[Tag 047G](https://kerodon.net/tag/047G)）。対応表の状態：なし。

total\_obj\_smallは各次数のSmallという宇宙の結論。原文の指定正則κでの本質的小さい模型へのcategorical equivalenceの存在は直接述べない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.HasSmallSimplexFibers.total_obj_small`

:::

:::corollary "kerodon_4_9_8_14"
Kerodon Corollary 4.9.8.14（[Tag 05PG](https://kerodon.net/tag/05PG)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：頂点と Δ¹ のファイバー・通常圏の局所小性と合成・濃度と正則性を照合。本質的 κ-small な内ファイブレーションを二つ合成したときの本質的小ささ。InnerFibration.comp は濃度を評価しない。

:::

:::proposition "kerodon_4_9_8_15"
Kerodon Proposition 4.9.8.15（[Tag 047F](https://kerodon.net/tag/047F)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：頂点と Δ¹ のファイバー・通常圏の局所小性と合成・濃度と正則性を照合。局所 κ-small な底の上の内ファイブレーションにおける本質的 κ-small 性の同値条件。通常圏の局所小性の伝播は Kan Hom の濃度を比較しない。

:::

:::corollary "kerodon_4_9_8_16"
Kerodon Corollary 4.9.8.16（[Tag 047K](https://kerodon.net/tag/047K)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後の宣言を含む）：頂点と Δ¹ のファイバー・通常圏の局所小性と合成・濃度と正則性を照合。局所 κ-small な底の上で本質的 κ-small な二つの内ファイブレーションを合成する条件。合成の内ファイブレーション性と違い局所・本質的小の両条件が必要。

:::

