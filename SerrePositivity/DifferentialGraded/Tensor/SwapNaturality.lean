module
public import SerrePositivity.DifferentialGraded.Tensor.Swap
public import SerrePositivity.DifferentialGraded.Module.LeftEquivalence

/-! # balanced tensor交換の左加群射に関する自然性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.BalancedTensor
open CategoryTheory MonoidalCategory Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma swapHom_naturality_left (M : RightModule A D) {N N' : LeftModuleCategory A D}
    (g : N ⟶ N') :
    map A D (𝟙 (ForgetEnrichment.of (Complex A) M)) g ≫
      swapHom A D M (ForgetEnrichment.to (Complex A) N') =
    swapHom A D M (ForgetEnrichment.to (Complex A) N) ≫
      map A Dᵒᵖ ((leftModuleToRightOpposite A D).map g)
        (𝟙 (ForgetEnrichment.of (Complex A) M.toFunctor)) := by
  apply hom_ext A D M (ForgetEnrichment.to (Complex A) N)
  intro x
  let gx : (ForgetEnrichment.to (Complex A) N).obj x ⟶
      (ForgetEnrichment.to (Complex A) N').obj x := (leftModuleEvaluation A D x).map g
  have h := ι_map A D (M := ForgetEnrichment.of (Complex A) M)
    (M' := ForgetEnrichment.of (Complex A) M) (𝟙 _) g x
  simp only [CategoryTheory.Functor.map_id] at h
  change ι A D M (ForgetEnrichment.to (Complex A) N) x ≫
      map A D (𝟙 (ForgetEnrichment.of (Complex A) M)) g =
    (𝟙 (M.obj (op x)) ⊗ₘ gx) ≫ ι A D M (ForgetEnrichment.to (Complex A) N') x at h
  have h' := ι_map A Dᵒᵖ (N := ForgetEnrichment.of (Complex A) M.toFunctor)
    (N' := ForgetEnrichment.of (Complex A) M.toFunctor)
    ((leftModuleToRightOpposite A D).map g) (𝟙 _) (op x)
  simp only [CategoryTheory.Functor.map_id, leftModuleToRightOpposite_map_eval] at h'
  change ι A Dᵒᵖ (ForgetEnrichment.to (Complex A) N).toRightOpposite M.toFunctor (op x) ≫
      map A Dᵒᵖ ((leftModuleToRightOpposite A D).map g)
        (𝟙 (ForgetEnrichment.of (Complex A) M.toFunctor)) =
    (gx ⊗ₘ 𝟙 (M.obj (op x))) ≫
      ι A Dᵒᵖ (ForgetEnrichment.to (Complex A) N').toRightOpposite M.toFunctor (op x) at h'
  calc
    _ = (𝟙 (M.obj (op x)) ⊗ₘ gx) ≫
        (signedSwap (M.obj (op x)) ((ForgetEnrichment.to (Complex A) N').obj x)).hom ≫
          ι A Dᵒᵖ (ForgetEnrichment.to (Complex A) N').toRightOpposite M.toFunctor (op x) := by
      rw [← Category.assoc, h, Category.assoc, ι_swapHom]
    _ = (signedSwap (M.obj (op x)) ((ForgetEnrichment.to (Complex A) N).obj x)).hom ≫
        (gx ⊗ₘ 𝟙 (M.obj (op x))) ≫
          ι A Dᵒᵖ (ForgetEnrichment.to (Complex A) N').toRightOpposite M.toFunctor (op x) := by
      rw [← Category.assoc, signedSwap_naturality, Category.assoc]
    _ = _ := by
      rw [ι_swapHom_assoc, h']

end SerrePositivity.DifferentialGraded.BalancedTensor
