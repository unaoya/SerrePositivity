module
public import SerrePositivity.DifferentialGraded.Complexes.TensorJoinAssociativity

/-! # 右因子を残す前方合成の左単位則 -/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory
variable {A : Type u} [CommRing A]

lemma tensorJoin_left_unit (E V R : Complex A) (e : 𝟙_ (Complex A) ⟶ E)
    (c : E ⊗ V ⟶ V) (hu : (λ_ V).inv ≫ e ▷ V ≫ c = 𝟙 V) :
    (λ_ (V ⊗ R)).inv ≫ e ▷ (V ⊗ R) ≫ (α_ E V R).inv ≫ c ▷ R = 𝟙 (V ⊗ R) := by
  have hunitTensor : (λ_ (V ⊗ R)).inv ≫ (α_ (𝟙_ (Complex A)) V R).inv = (λ_ V).inv ▷ R := by
    monoidal
  rw [associator_inv_naturality_left_assoc]
  calc
    _ = (λ_ V).inv ▷ R ≫ (e ▷ V) ▷ R ≫ c ▷ R := by
      simpa only [Category.assoc] using congrArg (fun t => t ≫ (e ▷ V) ▷ R ≫ c ▷ R) hunitTensor
    _ = ((λ_ V).inv ≫ e ▷ V ≫ c) ▷ R := by simp only [comp_whiskerRight]
    _ = 𝟙 _ := by rw [hu, id_whiskerRight]

end SerrePositivity.DifferentialGraded
