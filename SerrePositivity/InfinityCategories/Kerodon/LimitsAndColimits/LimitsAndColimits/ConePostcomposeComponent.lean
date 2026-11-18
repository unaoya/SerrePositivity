module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ConePostcomposeHomotopy
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ConeNaturality
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FixedHomotopyEvaluation

/-!
概要：通常の錐の後合成の指定ホモトピーは、任意の準圏へ写した後も頂点で可逆。
方針：既存の全ホモトピーと固定頂点の式をそのまま後合成し、元の評価法則を使う。
使われ方：Kerodon §7.1（Tag 02H1）、HTT 6.2.2.6 の二段分解の三角形。
規約：元の錐と指定自然変換を保持し、全錐の比較を作り直さない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 元の通常の全錐の指定変換を、同じ係数で写した全関手の射として使う。 -/
def nerveConePostcomposeHom {I C : Type u} [Category.{u} I] [Category.{u} C]
    {F G : I ⥤ C} (c : Cone F) (η : F ⟶ G) {X : SSet.{u}} (U : nerve C ⟶ X) :
    FunctorHom ((nerveCone c).val ≫ U) ((nerveCone ((Cone.postcompose η).obj c)).val ≫ U) :=
  SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
    (functorHomotopyPostcomp (nerveConePostcomposeHomotopy c η) U))

/-- 元の指定全錐の変換は、後合成した後も同じ錐頂点で可逆。 -/
lemma nerveConePostcomposeHom_apex_isIso {I C : Type u}
    [Category.{u} I] [Category.{u} C] {F G : I ⥤ C} (c : Cone F) (η : F ⟶ G)
    {X : SSet.{u}} (U : nerve C ⟶ X) :
    IsIso (functorHomEvaluate (nerveConePostcomposeHom c η U)
      (SSet.yonedaEquiv (joinInl (Δ[0] : SSet.{u}) (nerve I)))) := by
  let i := joinInl (Δ[0] : SSet.{u}) (nerve I)
  let H := functorHomotopyPostcomp (nerveConePostcomposeHomotopy c η) U
  have hi : i ≫ ((nerveCone c).val ≫ U) =
      i ≫ ((nerveCone ((Cone.postcompose η).obj c)).val ≫ U) := by
    rw [← Category.assoc, ← Category.assoc, nerveCone_point, nerveCone_point]
    rfl
  have hH : (i ▷ (Δ[1] : SSet.{u})) ≫ H.h =
      fst (Δ[0] : SSet.{u}) (Δ[1] : SSet.{u}) ≫ (i ≫ ((nerveCone c).val ≫ U)) := by
    change (i ▷ (Δ[1] : SSet.{u})) ≫ (nerveConePostcomposeHomotopy c η).h ≫ U = _
    rw [← Category.assoc, nerveConePostcomposeHomotopy_fixedVertex]
    simp only [i, Category.assoc]
  have hx : i.app (Opposite.op ⦋0⦌) (SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u}))) =
      SSet.yonedaEquiv i := by
    rw [← SSet.yonedaEquiv_comp, Category.id_comp]
  have h := functorHomEvaluate_isIso_of_fixedHomotopy H i hi hH
    (SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u})))
  rw [hx] at h
  exact h

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
