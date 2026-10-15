module

public import SerrePositivity.PerfectComplex.TensorTriple

/-! # Detecting maps from a tensor of three rank-one modules by one generator -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity
open CategoryTheory Category Limits MonoidalCategory
open scoped TensorProduct
variable {R : Type u} [CommRing R]

lemma moduleRankOne_smul_generator (M : ModuleCat.{u} R) (e : M ≅ ModuleCat.of R R) (x : M) :
    x = e.hom x • e.inv 1 := by
  calc
    x = e.inv (e.hom x) := (ModuleCat.inv_hom_apply e x).symm
    _ = _ := by
      simpa only [smul_eq_mul, mul_one] using e.inv.hom.map_smul (e.hom x) (1 : R)

lemma rankOneTensorTriple_hom_ext (M N T : ModuleCat.{u} R)
    (eM : M ≅ ModuleCat.of R R) (eN : N ≅ ModuleCat.of R R) (eT : T ≅ ModuleCat.of R R)
    {Y : ModuleCat.{u} R} {f g : (M ⊗ N) ⊗ T ⟶ Y}
    (h : f ((eM.inv 1 ⊗ₜ[R] eN.inv 1) ⊗ₜ[R] eT.inv 1) =
      g ((eM.inv 1 ⊗ₜ[R] eN.inv 1) ⊗ₜ[R] eT.inv 1)) : f = g := by
  apply ModuleCat.hom_ext
  apply TensorProduct.ext_threefold
  intro x y z
  change f.hom ((x ⊗ₜ[R] y) ⊗ₜ[R] z) = g.hom ((x ⊗ₜ[R] y) ⊗ₜ[R] z)
  rw [moduleRankOne_smul_generator M eM x, moduleRankOne_smul_generator N eN y,
    moduleRankOne_smul_generator T eT z]
  simp only [← TensorProduct.smul_tmul' (R := R) (R' := R),
    TensorProduct.tmul_smul (R := R) (R' := R), smul_smul]
  rw [f.hom.map_smul, g.hom.map_smul]
  exact congrArg (fun v => (eM.hom x * eN.hom y * eT.hom z) • v) h

end SerrePositivity
