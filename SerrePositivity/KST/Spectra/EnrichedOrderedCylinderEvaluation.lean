module

public import SerrePositivity.KST.Spectra.EnrichedOrderedCylinderBridge
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedParameterCylinderRestriction

/-!
概要：二段の円柱の比較と、評価パラメータの制限の厳密な両立。
方針：同じ段では元の関手、段をまたぐ場合は制限した自然変換を計算する。
規約：全 Hom パラメータを保持。使われ方：因子分解の外辺と基点評価の一致。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory MonoidalCategory SSet
namespace SerrePositivity.KST.Spectra.EnrichedOrderedCylinder
variable {C : Type v} {D : Type w} [EnrichedCategory SSet.{u} C] [EnrichedCategory SSet.{u} D]
  {A : SSet.{u}} (i : 𝟙_ SSet.{u} ⟶ A)
  (F G : EnrichedFunctor SSet.{u} C D)
  (θ : GradedNatTrans (Center.ofBraidedObj A) F G)

/-- 指定したパラメータの辺での評価は、制限した自然変換の円柱での評価と一致。 -/
lemma bridge_evaluation :
    (bridge (C := C) i).comp SSet (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.evaluationFunctor A F G θ) =
      (bridge (C := C) (𝟙 (𝟙_ SSet.{u}))).comp SSet
        (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.evaluationFunctor (𝟙_ SSet.{u}) F G
          (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.gradedRestriction i F G θ)) := by
  refine EnrichedFunctor.ext SSet ?_ ?_
  · rintro ⟨j, x⟩
    fin_cases j <;> rfl
  rintro ⟨j, x⟩ ⟨k, y⟩
  fin_cases j <;> fin_cases k
  all_goals
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    rintro ⟨p, f⟩
    rfl

end SerrePositivity.KST.Spectra.EnrichedOrderedCylinder
