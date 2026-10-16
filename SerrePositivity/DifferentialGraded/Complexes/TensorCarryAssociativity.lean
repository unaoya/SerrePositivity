module
public import SerrePositivity.DifferentialGraded.Complexes.TensorJoinAssociativity

/-! # 固定左tensor因子を伴う右作用の結合則 -/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory
variable {A : Type u} [CommRing A]

/-- 右作用の結合図式は固定左tensor因子を追加しても保たれる。 -/
lemma tensorCarry_assoc (K P Q R T U V : Complex A)
    (f : P ⊗ Q ⟶ T) (g : T ⊗ R ⟶ U) (h : Q ⊗ R ⟶ V) (k : P ⊗ V ⟶ U)
    (ha : (f ▷ R) ≫ g = (α_ P Q R).hom ≫ P ◁ h ≫ k) :
    (((α_ K P Q).hom ≫ K ◁ f) ▷ R) ≫ (α_ K T R).hom ≫ K ◁ g =
    (α_ (K ⊗ P) Q R).hom ≫ (K ⊗ P) ◁ h ≫ (α_ K P V).hom ≫ K ◁ k := by
  simp only [comp_whiskerRight, Category.assoc]
  rw [associator_naturality_middle_assoc, ← whiskerLeft_comp, ha]
  simp only [whiskerLeft_comp]
  rw [pentagon_assoc, associator_naturality_right_assoc]

end SerrePositivity.DifferentialGraded
