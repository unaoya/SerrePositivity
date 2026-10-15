module

public import SerrePositivity.KTheory.Adams.TensorCube
public import SerrePositivity.HomologicalAlgebra.KoszulOneCoordinates

/-! # The cubic rotation is trivial on the degree-zero scalar unit -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity
open CategoryTheory Category Limits MonoidalCategory HomologicalComplex TensorProduct
variable {R : Type u} [CommRing R]
namespace Adams

lemma scalarTriple_cyclic (x y z : R) :
    (x ⊗ₜ[R] y) ⊗ₜ[R] z = (z ⊗ₜ[R] x) ⊗ₜ[R] y := by
  let e : (ModuleCat.of R R ⊗ ModuleCat.of R R) ⊗ ModuleCat.of R R ≅ ModuleCat.of R R :=
    MonoidalCategory.tensorIso (λ_ (ModuleCat.of R R)) (Iso.refl _) ≪≫ λ_ (ModuleCat.of R R)
  apply e.toLinearEquiv.injective
  change (x * y) * z = (z * x) * y
  ring

lemma rankOneTriple_cyclic (M : ModuleCat.{u} R) (e : M ≅ ModuleCat.of R R)
    (x y z : M) : (x ⊗ₜ[R] y) ⊗ₜ[R] z = (z ⊗ₜ[R] x) ⊗ₜ[R] y := by
  let F := MonoidalCategory.tensorIso (MonoidalCategory.tensorIso e e) e
  apply F.toLinearEquiv.injective
  change (e.hom x ⊗ₜ[R] e.hom y) ⊗ₜ[R] e.hom z =
    (e.hom z ⊗ₜ[R] e.hom x) ⊗ₜ[R] e.hom y
  exact scalarTriple_cyclic _ _ _

lemma tensorCubeUnit_rotation : tensorCubeRotation (oneKoszulUnit (R := R)) = 𝟙 _ := by
  let U := oneKoszulUnit (R := R)
  apply HomologicalComplex.Hom.ext
  funext n
  apply cochainTensorTriple_hom_ext U U U n
  intro i j k h
  by_cases hi : i = 0
  · subst i
    by_cases hj : j = 0
    · subst j
      by_cases hk : k = 0
      · subst k
        have hn : n = 0 := by omega
        subst n
        apply ModuleCat.hom_ext
        apply TensorProduct.ext_threefold
        intro x y z
        change (tensorCubeRotation U).f 0
          (cochainTensorTripleι U U U 0 0 0 0 rfl ((x ⊗ₜ[R] y) ⊗ₜ[R] z)) =
          cochainTensorTripleι U U U 0 0 0 0 rfl ((x ⊗ₜ[R] y) ⊗ₜ[R] z)
        rw [tensorCubeRotation_apply_ι]
        simp only [zero_add, zero_mul, Int.negOnePow_zero, one_smul]
        exact congrArg (cochainTensorTripleι U U U 0 0 0 0 rfl)
          (rankOneTriple_cyclic (U.X 0) (oneKoszulUnitSelfIso (R := R)) x y z).symm
      · have hz := isZero_single_obj_X (.up ℤ) 0 (ModuleCat.of R R) k hk
        exact ((tensorLeft (U.X 0 ⊗ U.X 0 : ModuleCat.{u} R)).map_isZero hz).eq_of_src _ _
    · have hz := isZero_single_obj_X (.up ℤ) 0 (ModuleCat.of R R) j hj
      exact ((tensorRight (U.X k)).map_isZero
        ((tensorLeft (U.X 0)).map_isZero hz)).eq_of_src _ _
  · have hz := isZero_single_obj_X (.up ℤ) 0 (ModuleCat.of R R) i hi
    exact ((tensorRight (U.X k)).map_isZero
      ((tensorRight (U.X j)).map_isZero hz)).eq_of_src _ _

/-- Collapse the three scalar unit factors by the tensor unit comparisons. -/
def tensorCubeUnitIso : tensorCube (oneKoszulUnit (R := R)) ≅ oneKoszulUnit :=
  cochainTensorIso (cochainTensorLeftUnitor oneKoszulUnit) (Iso.refl _) ≪≫
    cochainTensorLeftUnitor oneKoszulUnit

end Adams
end SerrePositivity
