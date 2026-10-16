module
public import SerrePositivity.DifferentialGraded.Complexes.TensorJoinUnit

/-! # 右作用の単位と固定左tensor因子の整合性 -/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory
variable {A : Type u} [CommRing A]

/-- 右単位を固定左因子の内側へ移す構造式。 -/
lemma tensorCarry_right_unit (K P H T : Complex A) (e : 𝟙_ (Complex A) ⟶ H)
    (f : P ⊗ H ⟶ T) :
    (ρ_ (K ⊗ P)).inv ≫ (K ⊗ P) ◁ e ≫ (α_ K P H).hom ≫ K ◁ f =
      K ◁ ((ρ_ P).inv ≫ P ◁ e ≫ f) := by
  rw [associator_naturality_right_assoc, rightUnitor_tensor_inv]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, whiskerLeft_comp]

end SerrePositivity.DifferentialGraded
