import Verso
import VersoManual
import VersoBlueprint
import Mathlib.CategoryTheory.Adjunction.PartialAdjoint
import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.Adjunction
import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.AdjunctionMappingSpaces
import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.AdjunctionPinchedSpaces
import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.HomotopyCategory
import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatUnitHomCriterion
import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.ReflectiveInvertedHom
import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.ReflectiveLocalObjects
import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitMappingAdjunction

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "6.2 Adjoint Functors Between ∞-Categories" =>
%%%
number := false
tag := "kerodon-6-2"
%%%

Kerodon の 6.2 節（[Tag 02EH](https://kerodon.net/tag/02EH)）の項目と、SerrePositivity・Mathlib の宣言との対応。本文は対応表（research/kerodon-coverage）の判定の理由の要約で、Kerodon の本文の写しではない。

# 6.2.1 Adjunctions of ∞-Categories

%%%
number := false
tag := "kerodon-6-2-1"
%%%

Kerodon [Tag 02EJ](https://kerodon.net/tag/02EJ)

:::definition "kerodon_6_2_1_1" (lean := "SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction.mkOfHomTriangles, SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction, SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction.left_triangle_hom")
Kerodon Definition 6.2.1.1（[Tag 02EK](https://kerodon.net/tag/02EK)）。対応表の状態：本体にある。

仮定：∞ 圏間の F,G と、単位型・余単位型の 2 射のホモトピー類（Kerodon と一致）。結論：両 zigzag の像が hFun で単位子に等しければ QCatAdjunction。構造から三角恒等式を回収できる（一致）。

:::

:::definition "kerodon_6_2_1_2" (lean := "SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction, SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction.unitHom")
Kerodon Definition 6.2.1.2（[Tag 02EL](https://kerodon.net/tag/02EL)）。対応表の状態：本体にある。

仮定：∞ 圏間の F,G（Kerodon と一致）。結論：QCatAdjunction F G の存在が随伴の存在。unitHom は単位のホモトピー類で、余単位と二三角は構造に含む（一致）。

:::

:::definition "kerodon_6_2_1_3"
Kerodon Notation 6.2.1.3（[Tag 02EM](https://kerodon.net/tag/02EM)）。対応表の状態：一部。

QCatAdjunctionの存在量化は原文のFがleft adjoint・Gがright adjointであるという二つの条件を直接表す。Functor準圏のLFun/RFun全体の構成は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction`

:::

:::proposition "kerodon_6_2_1_4" (lean := "SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction, SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatHomFunctor, SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCellEquiv")
Kerodon Remark 6.2.1.4（[Tag 02EN](https://kerodon.net/tag/02EN)）。対応表の状態：本体にある。

仮定：∞ 圏間の F,G と単位・余単位のホモトピー類（Kerodon と一致）。結論：qcatCellEquiv で hFun の射と双圏の 2 射を対応させ、三角恒等式を持つものが QCatAdjunction（一致）。

:::

:::proposition "kerodon_6_2_1_8" (lean := "SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction.comp")
Kerodon Remark 6.2.1.8（[Tag 02ES](https://kerodon.net/tag/02ES)）。対応表の状態：本体にある。

仮定：三つの ∞ 圏と合成可能な随伴 F⊣G、F′⊣G′（Kerodon と一致）。結論：QCatAdjunction (F≫F′) (G′≫G)（一致）。

:::

:::proposition "kerodon_6_2_1_13"
Kerodon Proposition 6.2.1.13（[Tag 02EX](https://kerodon.net/tag/02EX)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：η と ε が指定充満部分圏上で同型となることを使う F,G の制限と同値。通常の Adjunction.restrict や QCatAdjunction の定義はこの選択による制限を述べない。

:::

:::proposition "kerodon_6_2_1_14"
Kerodon Proposition 6.2.1.14（[Tag 02EY](https://kerodon.net/tag/02EY)）。対応表の状態：一部。

QCatAdjunction.toHoAdjunctionは同じF,Gの随伴をホモトピー圏へ降ろすので原文(1)⇒(2)の方向。全試験準圏のHomを調べるunit判定は、hFとhGだけを使う逆判定の代用としない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcat_exists_adjunction_unitHom_iff`、`SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatAdjunctionOfUnitHomBijective`、`SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction.toHoAdjunction`

:::

:::corollary "kerodon_6_2_1_15" (lean := "SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction.toHoAdjunction, SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction.hoHomEquiv")
Kerodon Corollary 6.2.1.15（[Tag 02EZ](https://kerodon.net/tag/02EZ)）。対応表の状態：本体にある。

仮定：∞ 圏間の F,G と QCatAdjunction F G（Kerodon と一致）。結論：誘導された通常の関手 hF,hG に対する Adjunction hF hG（一致）。

:::

:::proposition "kerodon_6_2_1_17" (lean := "SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalMap_isSimplicialHomotopyEquivalence, SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.pinchedHomEquivalence")
Kerodon Proposition 6.2.1.17（[Tag 02F1](https://kerodon.net/tag/02F1)）。対応表の状態：本体にある。

仮定：∞ 圏間の随伴 a:F⊣G と各側の頂点 x,y（Kerodon と一致）。結論：単位による intervalMap a x y が単体的ホモトピー同値。従って hKan で同型（一致）。

:::

:::proposition "kerodon_6_2_1_19" (uses := "kerodon_1_4_0_1, kerodon_6_1_3_4, kerodon_6_1_3_8, kerodon_8_3_4_10")
Kerodon Remark 6.2.1.19（[Tag 02F3](https://kerodon.net/tag/02F3)）。対応表の状態：一部。

rightAdjointFunctorIsoは同じFの二つの右随伴G,G′のFunctor空間内の同型を直接構成する。LFunとRFunの反対の同値全体は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction.rightAdjointFunctorIso`、`SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction.rightAdjointIso`

:::

:::corollary "kerodon_6_2_1_21"
Kerodon Corollary 6.2.1.21（[Tag 06T9](https://kerodon.net/tag/06T9)）。対応表の状態：一部。

n=−2、D=Δ⁰に制限するとpointAdjunction\_isTerminalは同じ右随伴Gが点の頂点を終対象へ送ると直接返す。終対象の全Homの可縮性とpinched/interval比較により、この場合の(−2)-truncated対象の保存になる。一般n・任意Dは含まない。

宣言：`SerrePositivity.KST.LocalizingInvariants.pointAdjunction_isTerminal`、`SerrePositivity.KST.LocalizingInvariants.pointVertex_isTerminal`

:::

# 6.2.2 Reflective Subcategories

%%%
number := false
tag := "kerodon-6-2-2"
%%%

Kerodon [Tag 02F5](https://kerodon.net/tag/02F5)

:::definition "kerodon_6_2_2_1"
Kerodon Definition 6.2.2.1（[Tag 05YR](https://kerodon.net/tag/05YR)）。対応表の状態：一部。

C′をW-localな頂点で張るfull subcategoryに制限するとLocalEquivalenceHomは全てのそのZについての同じ前合成の同値性。isLocalForHom\_iff\_intervalで原文の写像空間作用と直接比較できる。任意のC′を名付ける述語は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsLocalForHom`、`SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.LocalEquivalenceHom`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.isLocalForHom_iff_interval`

:::

:::definition "kerodon_6_2_2_6" (uses := "kerodon_1_4_0_1")
Kerodon Definition 6.2.2.6（[Tag 02F6](https://kerodon.net/tag/02F6)）。対応表の状態：一部。

C′をW-local対象のfull subcategoryに限り、各xからそこへのlocal equivalenceを指定するとisReflectiveSubcategory\_of\_localReplacementsは同じ部分圏の反射を構成する。一般の反射・余反射の全定義は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.isReflectiveSubcategory_of_localReplacements`

:::

:::definition "kerodon_6_2_2_13"
Kerodon Variant 6.2.2.13（[Tag 06Y9](https://kerodon.net/tag/06Y9)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：本質的 κ-small な Kan 複体の切断が本質的 κ-small であり指定の共通部分が反射的となる結論。coskeleton の随伴に κ 評価はない。

:::

:::definition "kerodon_6_2_2_14"
Kerodon Variant 6.2.2.14（[Tag 05Q7](https://kerodon.net/tag/05Q7)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：QC の辺 F の切断条件と、濃度・局所次数で指定する QC の部分圏の比較。CatInfinity と宇宙 lift には整数次数と基数の組がない。

:::

:::proposition "kerodon_6_2_2_16"
Kerodon Proposition 6.2.2.16（[Tag 03XA](https://kerodon.net/tag/03XA)）。対応表の状態：なし。

引用はreflectorがfを反転することと局所性のiff。原文の(2)〜(5)のcoslice制限やouter horn充填と同じ条件ではなく、原文の五条件の同値の方向を直接返さない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.reflective_isIso_map_iff_localHom`、`SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.reflective_localEquivalenceHom_iff`

:::

:::corollary "kerodon_6_2_2_17"
Kerodon Corollary 6.2.2.17（[Tag 04JD](https://kerodon.net/tag/04JD)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：充満部分圏上の図式 q に対する slice の辺が元の C′-local equivalence のときの局所同値性。IsLocalForHom の比較だけでは slice の局所 Hom を同定しない。

:::

:::corollary "kerodon_6_2_2_18"
Kerodon Corollary 6.2.2.18（[Tag 04JE](https://kerodon.net/tag/04JE)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：反射的 C′ の図式 q 上の slice が C の同じ図式上の slice に反射的。通常圏の Over の随伴と、任意の単体図式の slice を区別した。

:::

:::proposition "kerodon_6_2_2_19"
Kerodon Proposition 6.2.2.19（[Tag 02FA](https://kerodon.net/tag/02FA)）。対応表の状態：一部。

ReflectiveSubcategoryの随伴からreflectionMappingEquivalenceと同じunitのadjunct比較を使えば、各xのunitが同じPに関するreflectionとなる。包含が左随伴を持つ⇒reflectiveという反射側の方向のみ。

宣言：`SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ReflectiveSubcategory`、`SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ReflectiveSubcategory.reflectionMappingEquivalence`、`SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.isReflectiveSubcategory_of_localReplacements`、`SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.exists_qcatAdjunction_of_commaFiberInitial`、`SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.pinchedMap_comparisonIso`

:::

:::definition "kerodon_6_2_2_20"
Kerodon Definition 6.2.2.20（[Tag 02FB](https://kerodon.net/tag/02FB)）。対応表の状態：一部。

選んだ反射rについてlocalizationとunitは原文のLと指定ηの構成を直接与える。任意の指定ηがreflection functorを与えるという述語・coreflectionの定義全体は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ReflectiveSubcategory.localization`、`SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ReflectiveSubcategory.unit`

:::

:::lemma_ "kerodon_6_2_2_23" (uses := "kerodon_1_4_0_1, kerodon_5_1_1_1, kerodon_5_1_2_3, kerodon_5_1_4_1, kerodon_5_2_2_8")
Kerodon Lemma 6.2.2.23（[Tag 02FD](https://kerodon.net/tag/02FD)）。対応表の状態：一部。

選んだReflectiveSubcategoryのreflectorとunit、および同じunitの写像空間比較から、原文のreflective⇒L,ηの存在という方向を直接得る。任意のηから随伴を回収する逆は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ReflectiveSubcategory`、`SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ReflectiveSubcategory.reflectionMappingEquivalence`、`SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.pinchedMap_comparisonIso`

:::

:::proposition "kerodon_6_2_2_24" (uses := "kerodon_1_4_0_1, kerodon_4_4_4_4, kerodon_6_1_4_6, kerodon_6_2_1_1, kerodon_6_2_1_17")
Kerodon Proposition 6.2.2.24（[Tag 02FE](https://kerodon.net/tag/02FE)）。対応表の状態：一部。

reflectedUnitIsoとunitOnInclusionIsoは、同じ反射随伴のunitについて原文(1)⇒(3)のLηと部分圏上のηの可逆性を直接返す。ηだけからの逆判定と任意counitの主張は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.ReflectiveSubcategory.reflectedUnitIso`、`SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.ReflectiveSubcategory.unitOnInclusionIso`、`SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ReflectiveSubcategory.reflectionMappingEquivalence`、`SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ReflectiveSubcategory`

:::

:::corollary "kerodon_6_2_2_26"
Kerodon Corollary 6.2.2.26（[Tag 02FF](https://kerodon.net/tag/02FF)）。対応表の状態：一部。

原文(2)に加え、GによるFunctor(Y,−)のホモトピー圏上の後合成が充満忠実と強めるとcounitHom\_isIso\_of\_postcompFullyFaithfulは同じ随伴のcounitを可逆にし(3)を直接返す。G自体の充満忠実性だけから追加条件を回収する部分は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction.counitHom_isIso_of_postcompFullyFaithful`、`SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.ReflectiveSubcategory.counitIso`、`SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.bicategory_counit_isIso_of_postcomp_fullyFaithful`

:::

:::corollary "kerodon_6_2_2_28"
Kerodon Corollary 6.2.2.28（[Tag 03UZ](https://kerodon.net/tag/03UZ)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：∞ 圏同値と、同型を反映し充満忠実な右随伴を持つことの同値。通常圏の反射的関手の同値判定と、QCat の unit/counit 判定は仮定の形が異なる。

:::

:::corollary "kerodon_6_2_2_29"
Kerodon Corollary 6.2.2.29（[Tag 02FG](https://kerodon.net/tag/02FG)）。対応表の状態：一部。

L,ηを選んだ反射随伴rのlocalizationとunitと仮定すると、unitOnLocalizationIsoとreflectedUnitIsoから原文(1)のη\_LとLηの可逆性を直接得る。任意のreflection functorから随伴を作る逆は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.ReflectiveSubcategory.idempotentIso`、`SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.ReflectiveSubcategory.unitOnLocalizationIso`

:::

# 6.2.3 Local Objects

%%%
number := false
tag := "kerodon-6-2-3"
%%%

Kerodon [Tag 04KG](https://kerodon.net/tag/04KG)

:::definition "kerodon_6_2_3_1"
Kerodon Definition 6.2.3.1（[Tag 02FZ](https://kerodon.net/tag/02FZ)）。対応表の状態：一部。

IsLocalForHomとIsLocalObjectは同じhomotopy classによる前合成の同値性を定義し、isLocalForHom\_iff\_intervalで原文の写像空間作用と一致する。w-local・W-localの二条件のみで、colocal側は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsLocalForHom`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsLocalObject`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.isLocalForHom_iff_interval`

:::

:::proposition "kerodon_6_2_3_9"
Kerodon Proposition 6.2.3.9（[Tag 06TA](https://kerodon.net/tag/06TA)）。対応表の状態：なし。

引用は可逆counitを持つ随伴から左関手が局所化となる逆向き。原文の局所化Fと右随伴GからGの充満忠実性・本質的像の判定を結論する型ではない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.isLocalization`

:::

:::corollary "kerodon_6_2_3_10" (lean := "SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.reflective_isLocal_iff_invertedEdges, SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.ReflectiveSubcategory.isLocal_iff_essentialImage, SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.reflective_localEquivalences_eq")
Kerodon Corollary 6.2.3.10（[Tag 06TB](https://kerodon.net/tag/06TB)）。対応表の状態：本体にある。

仮定：∞ 圏 X の反射的部分圏と、反射が可逆にする辺の族 W（Kerodon と一致）。結論：W-局所であることと部分圏の頂点に同型であることが同値。局所同値の辺の族は W と一致（一致）。

:::

:::definition "kerodon_6_2_3_11"
Kerodon Definition 6.2.3.11（[Tag 02G0](https://kerodon.net/tag/02G0)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：辺の集合 W が localizing であることを恒等・合成・局所対象への置換と双対条件で定める述語。IsLocalization は指定された射の普遍性。

:::

:::proposition "kerodon_6_2_3_14"
Kerodon Proposition 6.2.3.14（[Tag 05Z2](https://kerodon.net/tag/05Z2)）。対応表の状態：なし。

局所置換から反射を構成する型と反射が反転する辺の集合の閉性は、原文の(a)〜(d)の同じ仮定間の含意を直接返さない。localizing条件や(d)との比較が不足する。

宣言：`SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.isReflectiveSubcategory_of_localReplacements`、`SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.reflective_localEquivalences_eq`

:::

:::corollary "kerodon_6_2_3_15"
Kerodon Corollary 6.2.3.15（[Tag 02G8](https://kerodon.net/tag/02G8)）。対応表の状態：なし。

引用は指定反射からinvertedEdgesの局所同値閉性と指定W-local部分圏の局所対象の同定。原文のlocalizing collectionsとreplete reflective subcategoriesの全単射を直接構成せず、その商・逆写像への比較がない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.reflective_localEquivalences_eq`、`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.reflective_isLocal_iff_localObject`

:::

:::corollary "kerodon_6_2_3_16"
Kerodon Corollary 6.2.3.16（[Tag 06TC](https://kerodon.net/tag/06TC)）。対応表の状態：一部。

原文のlocalizingの仮定に各xのW-local replacementの存在を明示的に追加すれば、isReflectiveSubcategory\_of\_localReplacementsは同じW-local部分圏の反射随伴を直接作り(1),(2)を与える。元のWと反転される辺の一致および(3),(4)は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.isReflectiveSubcategory_of_localReplacements`、`SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.reflective_localEquivalences_eq`、`SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ReflectiveSubcategory.isLocalization`

:::

:::definition "kerodon_6_2_3_17"
Kerodon Notation 6.2.3.17（[Tag 02G4](https://kerodon.net/tag/02G4)）。対応表の状態：一部。

localObjectsSubcomplexは原文がC\[W⁻¹\]と名付ける同じW-local頂点で張るfull subcategoryを直接構成する。局所化としての普遍性は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.localObjectsSubcomplex`

:::

# 6.2.4 Stability Properties of Reflective Subcategories

%%%
number := false
tag := "kerodon-6-2-4"
%%%

Kerodon [Tag 05Z3](https://kerodon.net/tag/05Z3)

:::lemma_ "kerodon_6_2_4_1"
Kerodon Lemma 6.2.4.1（[Tag 05Z1](https://kerodon.net/tag/05Z1)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：指定した C′ と W の片側取消し・C′ への置換から反射と W の同定を導く結論。W-局所対象を先に定める局所置換の補題では任意の C′ の同定がない。

:::

:::proposition "kerodon_6_2_4_2"
Kerodon Proposition 6.2.4.2（[Tag 02SV](https://kerodon.net/tag/02SV)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：cocartesian fibration による反射的部分圏の引き戻しと、局所同値の cocartesian な辺による判定。通常の反射からの局所化には底変換がない。

:::

:::proposition "kerodon_6_2_4_3"
Kerodon Proposition 6.2.4.3（[Tag 05Z4](https://kerodon.net/tag/05Z4)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：cocartesian fibration の各ファイバーの反射と輸送による局所同値保存から大域的反射性を得る主張。各ファイバーの随伴データを全空間に貼る型がない。

:::

:::proposition "kerodon_6_2_4_5"
Kerodon Proposition 6.2.4.5（[Tag 05Z6](https://kerodon.net/tag/05Z6)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：cartesian fibration の反変輸送が指定された反射的ファイバー部分圏を保つときの大域的反射性。op で辺を反転する補題はファイバー反射を組み立てない。

:::

:::corollary "kerodon_6_2_4_8"
Kerodon Corollary 6.2.4.8（[Tag 05Z9](https://kerodon.net/tag/05Z9)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：oriented fiber product の指定充満部分圏で、射影の像の cocartesian 性等による局所同値の判定。laxPullbackEquivalenceSubcomplex の充満忠実性は局所同値を分類しない。

:::

:::corollary "kerodon_6_2_4_9"
Kerodon Corollary 6.2.4.9（[Tag 05ZA](https://kerodon.net/tag/05ZA)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：oriented fiber product の反射に伴う局所同値と三つの射影条件の同値。pullback 射影の cartesian 性だけでは反射の像が決まらない。

:::

# 6.2.5 Correspondences

%%%
number := false
tag := "kerodon-6-2-5"
%%%

Kerodon [Tag 02FJ](https://kerodon.net/tag/02FJ)

:::lemma_ "kerodon_6_2_5_1" (uses := "kerodon_1_4_0_1, kerodon_5_1_2_3, kerodon_6_2_2_6")
Kerodon Lemma 6.2.5.1（[Tag 02FK](https://kerodon.net/tag/02FK)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：Δ¹ 上の fibration の crossing edge の cartesian/cocartesian 性をファイバーへの反射・余反射で判定する結果。標準 collage の構造射の持ち上げは任意の crossing edge を判定しない。

:::

:::corollary "kerodon_6_2_5_2" (uses := "kerodon_1_4_0_1, kerodon_5_1_4_1")
Kerodon Corollary 6.2.5.2（[Tag 02FL](https://kerodon.net/tag/02FL)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：任意の E→Δ¹ の cartesian 性と左ファイバーの余反射性、cocartesian 性と右ファイバーの反射性の同値。Quillen cf collage はモデル圏由来の特例。

:::

:::proposition "kerodon_6_2_5_4" (uses := "kerodon_1_4_0_1, kerodon_5_1_1_1, kerodon_5_1_2_3, kerodon_5_1_4_1, kerodon_6_2_1_8, kerodon_6_2_1_17, kerodon_6_2_2_23, kerodon_6_2_2_24, kerodon_6_2_5_2")
Kerodon Proposition 6.2.5.4（[Tag 02FN](https://kerodon.net/tag/02FN)）。対応表の状態：一部。

EをQuillenのcf collage、Fをその指定共変輸送の左導来関手に制限すると、quillenCfDerivedAdjunction\_existsとcartesian射影の型は原文の同じ輸送の右随伴およびUのcartesian性を直接与える。一般の模型圏・単体豊穣・SM7・関手的分解を仮定し、具体例のModelCategory instanceなし（§6）。一般のEのiffは含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.quillenCfDerivedAdjunction_exists`、`SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.quillenCfCollageProjection_cartesianFibration`、`SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitIntervalMap_isSimplicialHomotopyEquivalence_of_collage`、`SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalPrecompose_equivalence_of_cocartesianHomotopy`、`SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfLeftDerived_transport`

:::

:::corollary "kerodon_6_2_5_5" (uses := "kerodon_1_1_0_6, kerodon_5_1_4_1, kerodon_6_2_5_4")
Kerodon Corollary 6.2.5.5（[Tag 06MB](https://kerodon.net/tag/06MB)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：任意の inner fibration で局所的な左右の lift の条件が同値となり、底辺ごとの輸送が随伴する結論。Quillen の随伴を入力する collage からの型とは向きが逆。

:::

:::lemma_ "kerodon_6_2_5_6" (uses := "kerodon_1_1_0_6, kerodon_1_2_5_1, kerodon_5_1_1_1, kerodon_5_1_2_3, kerodon_5_1_4_1")
Kerodon Lemma 6.2.5.6（[Tag 05Q8](https://kerodon.net/tag/05Q8)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：cocartesian fibration の下で、同じ辺の大域・局所 cartesian 性が同値。CartesianInitialBoundary の op での持ち上げ補題は逆向きの局所判定を述べない。

:::

:::proposition "kerodon_6_2_5_7" (uses := "kerodon_1_1_0_6, kerodon_5_1_1_1, kerodon_5_1_4_1, kerodon_6_2_5_5, kerodon_6_2_5_6")
Kerodon Proposition 6.2.5.7（[Tag 02FP](https://kerodon.net/tag/02FP)）。対応表の状態：一部。

UをQuillenのcf collage射影に限ればquillenCfCollageProjection\_cartesianFibrationは原文(2)のcartesian性を直接返す。ModelCategory C,D・単体豊穣・SM7・関手的分解を仮定し具体例のinstanceなし（§6）。全辺の輸送の随伴と一般Uのiffは含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.quillenCfDerivedAdjunction_exists`、`SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.quillenCfCollageProjection_cartesianFibration`、`SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitIntervalMap_isSimplicialHomotopyEquivalence_of_collage`、`SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalPrecompose_equivalence_of_cocartesianHomotopy`、`SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfLeftDerived_transport`

:::

# 6.2.6 Local Existence Criterion

%%%
number := false
tag := "kerodon-6-2-6"
%%%

Kerodon [Tag 02FQ](https://kerodon.net/tag/02FQ)

:::proposition "kerodon_6_2_6_1" (uses := "kerodon_1_2_5_1, kerodon_1_4_0_1, kerodon_5_1_2_3, kerodon_5_1_4_1, kerodon_5_2_3_15, kerodon_6_2_1_17, kerodon_6_2_5_4")
Kerodon Proposition 6.2.6.1（[Tag 02FV](https://kerodon.net/tag/02FV)）。対応表の状態：なし。

引用の右辺は共変Hom関手とのFunctorIsoの存在。原文が指定する単一辺uを使う各Hom作用との比較が型にない。commaの始対象から随伴を作る補題も、その同じuの普遍性との橋を欠く。

宣言：`SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.exists_leftAdjoint_iff_covariantHom_representable`、`SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.exists_qcatAdjunction_of_commaFiberInitial`

:::

:::corollary "kerodon_6_2_6_2" (uses := "kerodon_1_4_0_1, kerodon_5_6_5_1, kerodon_5_6_6_1, kerodon_5_6_6_10, kerodon_5_6_6_21, kerodon_6_2_6_1")
Kerodon Corollary 6.2.6.2（[Tag 02J9](https://kerodon.net/tag/02J9)）。対応表の状態：一部。

exists\_qcatAdjunction\_of\_commaFiberInitialは原文と同じD×\_C C\_\{X/\}の全fiberの始対象から左随伴を作るので(3)⇒(1)を直接返す。任意left fibrationや全五条件の同値は含まない。

宣言：`SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.exists_qcatAdjunction_of_commaFiberInitial`、`SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcat_exists_adjunction_unitHom_iff_commaInitial`

:::

:::corollary "kerodon_6_2_6_4" (lean := "CategoryTheory.Functor.isRightAdjoint_iff_leftAdjointObjIsDefined_eq_top")
Kerodon Corollary 6.2.6.4（[Tag 02FW](https://kerodon.net/tag/02FW)）。対応表の状態：Mathlib にある。

仮定：通常の圏間の関手 G:D→C（Kerodon と一致）。結論：G が右随伴であることと leftAdjointObjIsDefined G が全対象で成立することが同値。その述語は Hom(x,G−) の余表現可能性（一致）。

:::

:::corollary "kerodon_6_2_6_5" (lean := "SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcat_exists_adjunction_unitHom_iff_unitMappingSpaceCondition, SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcat_exists_adjunction_unitHom_iff")
Kerodon Corollary 6.2.6.5（[Tag 02FX](https://kerodon.net/tag/02FX)）。対応表の状態：本体にある。

仮定：∞ 圏間の F,G と単位型の自然変換のホモトピー類 η（Kerodon と一致）。結論：η を単位に持つ随伴の存在と、各頂点対で単位が誘導する写像空間の比較が単体的ホモトピー同値であることが同値（一致）。

:::

:::corollary "kerodon_6_2_6_6"
Kerodon Corollary 6.2.6.6（[Tag 02KD](https://kerodon.net/tag/02KD)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：右随伴 G が任意の図式 u に対して誘導する coslice 比較も右随伴を持つこと。通常の圏の under や随伴の Hom 全単射は単体図式 u を扱わない。

:::

# 6.2.7 Digression: ∞-Categories with Short Morphisms

%%%
number := false
tag := "kerodon-6-2-7"
%%%

Kerodon [Tag 03XB](https://kerodon.net/tag/03XB)

:::definition "kerodon_6_2_7_1"
Kerodon Definition 6.2.7.1（[Tag 03XC](https://kerodon.net/tag/03XC)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：S の辺に沿う 2-単体の因子化を指定の普遍性で optimal とする定義。一般の射の factorization のデータにはこの普遍性がない。

:::

:::definition "kerodon_6_2_7_4"
Kerodon Definition 6.2.7.4（[Tag 03XG](https://kerodon.net/tag/03XG)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：恒等・同型条件と S-optimal factorization などで定義する short morphism のクラス。MorphismProperty の通常の閉性だけでは一連の公理を表さない。

:::

:::definition "kerodon_6_2_7_6"
Kerodon Notation 6.2.7.6（[Tag 03XJ](https://kerodon.net/tag/03XJ)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：隣接辺の条件で C の短射部分複体 C\^short を作る定義。全頂点での充満部分複体や core では選別する辺が異なる。

:::

:::theorem "kerodon_6_2_7_10"
Kerodon Theorem 6.2.7.10（[Tag 03XN](https://kerodon.net/tag/03XN)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：C\^short⊂C の内アノダイン性。spine の標準単体への包含は対象 C の short morphism による部分複体を扱わない。

:::

:::definition "kerodon_6_2_7_12"
Kerodon Notation 6.2.7.12（[Tag 03XQ](https://kerodon.net/tag/03XQ)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：f を short 辺で分解する最小の長さ ℓ(f) とその基本性質。通常の鎖の length は ∞ 圏の射の最小分解ではない。

:::

:::lemma_ "kerodon_6_2_7_13"
Kerodon Lemma 6.2.7.13（[Tag 03XR](https://kerodon.net/tag/03XR)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：三角形の optimal factorization と両辺の ℓ の評価。内ホーンの合成や通常のリスト長の加法性にこの最小分解条件がない。

:::

:::definition "kerodon_6_2_7_14"
Kerodon Notation 6.2.7.14（[Tag 03XT](https://kerodon.net/tag/03XT)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：単体の principal rank と面を取った場合の階数の不等式。単体の次数や退化の判定では short 辺の最初の位置を測らない。

:::

:::lemma_ "kerodon_6_2_7_15"
Kerodon Lemma 6.2.7.15（[Tag 03XU](https://kerodon.net/tag/03XU)）。対応表の状態：なし。

B6再検索（現本体・ロックMathlib、移動後を含む）：非 short な単体 σ へ選んだ σ⁺ を割り当て、面と指定三角形が条件を満たす関数。spine の個別のホーン充填ではこの一貫した割当てがない。

:::

