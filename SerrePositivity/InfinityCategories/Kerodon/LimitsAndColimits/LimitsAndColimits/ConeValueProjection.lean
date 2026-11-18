module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.ConeFamilyApex
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHomEvaluation
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FunctorComparison.FunctorIsoPointEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.HoHomVertexTransport

/-!
概要：元の錐圏から全錐の関手圏への射影と、頂点・底の厳密な式。
方針：既存の slice と錐の fiber の比較を、同じ fiber の包含へ合成する。
使われ方：Kerodon §7.1（Tag 02H1）、HTT 6.2.2.6 の元の錐の余単位の比較。
規約：元の錐と全射を保持し、底の図式は厳密に固定する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 元の錐の全関手を、元の図式に関する fiber の包含で回収する。 -/
def coneValueProjection {K X : SSet.{u}} (p : K ⟶ X) :
    sliceOver p ⟶ (ihom (join (Δ[0] : SSet.{u}) K)).obj X :=
  sliceConeFamilyMap p ≫ vertexFiberι (coneRestriction K X) (functorVertex p)

/-- 元の各錐の値は、その錐の全射の元の関手頂点に等しい。 -/
lemma coneValueProjection_vertex {K X : SSet.{u}} (p : K ⟶ X) (c : JoinCone p) :
    (coneValueProjection p).app (Opposite.op ⦋0⦌) c = functorVertex c.val := by
  change ((sliceConeFamilyMap p).app (Opposite.op ⦋0⦌) c).val = _
  rw [sliceConeFamilyMap_app_zero]
  rfl

/-- 全関手の左頂点での評価は、元の錐圏の頂点射影と厳密に一致する。 -/
lemma coneValueProjection_apex {K X : SSet.{u}} (p : K ⟶ X) :
    coneValueProjection p ≫ evaluateFunctorAt (SSet.yonedaEquiv (joinInl (Δ[0] : SSet.{u}) K)) =
      sliceOverProjection p := by
  have he := SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointPrecomp_evaluation
    (X := X) (SSet.yonedaEquiv (joinInl (Δ[0] : SSet.{u}) K))
  simp only [Equiv.symm_apply_apply] at he
  rw [← he]
  simpa only [coneValueProjection, coneFamilyApex, Category.assoc] using sliceConeFamilyMap_apex p

/-- 全関手を底へ制限したものは、元の図式の定値族そのもの。 -/
lemma coneValueProjection_boundary {K X : SSet.{u}} (p : K ⟶ X) :
    coneValueProjection p ≫ coneRestriction K X = SSet.const (functorVertex p) := by
  rw [coneValueProjection, Category.assoc, vertexFiberι_comp, SSet.comp_const]

/-- 元の錐圏の射を、その全関手の間の同じ射として回収する。 -/
def coneHoMorphismValue {K X : SSet.{u}} [Quasicategory X] {p : K ⟶ X}
    {c d : JoinCone p} (β : (SSet.HomotopyCategory.mk c : hoFunctor.obj (sliceOver p)) ⟶
      SSet.HomotopyCategory.mk d) : FunctorHom c.val d.val :=
  hoHomMapWithVertexEqualities (coneValueProjection p)
    (coneValueProjection_vertex p c) (coneValueProjection_vertex p d) β

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
