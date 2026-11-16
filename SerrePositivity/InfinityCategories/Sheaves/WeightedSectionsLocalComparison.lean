module

public import SerrePositivity.InfinityCategories.Sheaves.WeightedSectionsData
public import SerrePositivity.InfinityCategories.Sheaves.WeightedSectionsValueTransport
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RightKanLimitVertexTransport

/-!
概要：元の重み付き切断の値を、実際の Yoneda の同じ形状の指定局所極限と比較する。
方針：選んだ同じ全関手の指定極限を取り出し、検証済みの全族同型で頂点を比較する。
  文献対応：HTT 5.1.5.6、Kerodon Definition 7.3.1.2（Tag 02Y9）、S8 の離散重みへの接続。
規約：比較先の錐とその極限性を明示し、存在だけの比較に置き換えない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
namespace SerrePositivity.InfinityCategories.Sheaves
variable {C : Type u} [SmallCategory C] {E : SSet.{u + 1}} [Quasicategory E]

/-- 元の全切断関手の値と、実際の Yoneda の同じ形状の指定局所極限の頂点比較。
HTT 5.1.5.6、Kerodon Definition 7.3.1.2（Tag 02Y9）、全族同型と極限の一意性の移送則。 -/
def weightedSections_nativeShapeLimitIso (O : Presheaf C E)
    (hE : SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E)
    (P : (PresheafCat C SpaceInfinity.{u}).op _⦋0⦌)
    (d : JoinCone (rightKanDiagram (nativeSetShapeOppositeYoneda C) O P))
    (hd : IsLimitCone d) : VertexIso ((weightedSections O hE).app _ P) d.vertex := by
  let c := (weightedSections_valueTransport O hE P).cone
  have hc := And.intro (weightedSections_valueTransport_isLimit O hE P)
    (weightedSections_valueTransport_vertex O hE P)
  have e := rightKanLimitVertexIsoOfFunctorIso (fixedOppositeSetYoneda_nativeIso C) O P c d hc.1 hd
  exact hc.2 ▸ e

end SerrePositivity.InfinityCategories.Sheaves
