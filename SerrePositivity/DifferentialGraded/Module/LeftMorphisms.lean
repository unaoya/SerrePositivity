module
public import SerrePositivity.DifferentialGraded.Module.LeftCategory
public import SerrePositivity.DifferentialGraded.Module.ActionChain

/-! # 左dg加群の閉零射と全次数作用の可換性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 左閉零射を二重opposite表示の全次数自然変換として読む。 -/
def leftModuleClosedHomEquiv (M N : LeftModuleCategory A D) :
    (M ⟶ N) ≃ ModuleParamTrans A Dᵒᵖ (𝟙_ (Complex A))
      (ForgetEnrichment.to (Complex A) M).toRightOpposite
      (ForgetEnrichment.to (Complex A) N).toRightOpposite :=
  moduleHomEquiv A Dᵒᵖ _ _ _

lemma leftModuleEvaluation_map (x : D) {M N : LeftModuleCategory A D} (f : M ⟶ N) :
    (leftModuleEvaluation A D x).map f =
      closedTransApp A (leftModuleClosedHomEquiv A D M N f) (op (op x)) := rfl

/-- 左加群の実際の射は、任意次数のHomに対するtensor作用と可換。 -/
lemma leftModuleMorphism_action_chain {M N : LeftModuleCategory A D} (f : M ⟶ N) (x y : D) :
    uncurryRight ((ForgetEnrichment.to (Complex A) M).map x y) ≫
      (leftModuleEvaluation A D y).map f =
    (𝟙 (x ⟶[Complex A] y) ⊗ₘ (leftModuleEvaluation A D x).map f) ≫
      uncurryRight ((ForgetEnrichment.to (Complex A) N).map x y) := by
  let τ := leftModuleClosedHomEquiv A D M N f
  have h := closedFamily_action_chain A
    (M := (ForgetEnrichment.to (Complex A) M).toRightOpposite)
    (N := (ForgetEnrichment.to (Complex A) N).toRightOpposite)
    (closedTransApp A τ) (closedTransApp_naturality A τ) (op (op x)) (op (op y))
  change uncurryRight (𝟙 _ ≫ (ForgetEnrichment.to (Complex A) M).map x y) ≫
      closedTransApp A τ (op (op y)) =
    (𝟙 (x ⟶[Complex A] y) ⊗ₘ closedTransApp A τ (op (op x))) ≫
      uncurryRight (𝟙 _ ≫ (ForgetEnrichment.to (Complex A) N).map x y) at h
  simpa only [Category.id_comp, leftModuleEvaluation_map] using h

end SerrePositivity.DifferentialGraded
