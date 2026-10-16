module
public import SerrePositivity.DifferentialGraded.Complexes.TensorJoinUnit

/-! # 中間の単位挿入と前方合成の単位律 -/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory
variable {A : Type u} [CommRing A]

lemma tensorMiddle_left_unit (E H P : Complex A) (e : 𝟙_ (Complex A) ⟶ H)
    (f : H ⊗ P ⟶ P) (hu : (λ_ P).inv ≫ e ▷ P ≫ f = 𝟙 P) :
    (((ρ_ E).inv ≫ E ◁ e) ▷ P) ≫ (α_ E H P).hom ≫ E ◁ f = 𝟙 (E ⊗ P) := by
  have hunit : (ρ_ E).inv ▷ P ≫ (α_ E (𝟙_ (Complex A)) P).hom = E ◁ (λ_ P).inv := by
    monoidal
  rw [comp_whiskerRight, Category.assoc, associator_naturality_middle_assoc]
  calc
    _ = E ◁ (λ_ P).inv ≫ E ◁ (e ▷ P) ≫ E ◁ f := by
      simpa only [Category.assoc] using congrArg (fun t => t ≫ E ◁ (e ▷ P) ≫ E ◁ f) hunit
    _ = E ◁ ((λ_ P).inv ≫ e ▷ P ≫ f) := by simp only [whiskerLeft_comp]
    _ = 𝟙 _ := by rw [hu, whiskerLeft_id]

lemma tensorSandwich_append (E H P : Complex A) (e : 𝟙_ (Complex A) ⟶ H)
    (f : H ⊗ P ⟶ P) (hu : (λ_ P).inv ≫ e ▷ P ≫ f = 𝟙 P) :
    (((λ_ E).inv ≫ (e ⊗ₘ ((ρ_ E).inv ≫ (𝟙 E ⊗ₘ e)))) ▷ P) ≫
      (α_ H (E ⊗ H) P).hom ≫ H ◁ ((α_ E H P).hom ≫ E ◁ f) =
    (λ_ (E ⊗ P)).inv ≫ e ▷ (E ⊗ P) := by
  have hunit : (λ_ E).inv ▷ P ≫ (α_ (𝟙_ (Complex A)) E P).hom = (λ_ (E ⊗ P)).inv := by
    monoidal
  simp only [tensorHom_def, comp_whiskerRight, id_whiskerRight, Category.id_comp, Category.assoc]
  rw [associator_naturality_middle_assoc, associator_naturality_left_assoc]
  rw [← whiskerLeft_comp, tensorMiddle_left_unit E H P e f hu, whiskerLeft_id, Category.comp_id]
  simpa only [Category.assoc] using congrArg (fun t => t ≫ e ▷ (E ⊗ P)) hunit

lemma tensorJoin_right_unit (V H R : Complex A) (e : 𝟙_ (Complex A) ⟶ H)
    (c : V ⊗ H ⟶ V) (hu : (ρ_ V).inv ≫ V ◁ e ≫ c = 𝟙 V) :
    V ◁ ((λ_ R).inv ≫ e ▷ R) ≫ (α_ V H R).inv ≫ c ▷ R = 𝟙 (V ⊗ R) := by
  have hunit : V ◁ (λ_ R).inv ≫ (α_ V (𝟙_ (Complex A)) R).inv = (ρ_ V).inv ▷ R := by
    monoidal
  simp only [whiskerLeft_comp, Category.assoc]
  rw [associator_inv_naturality_middle_assoc]
  calc
    _ = (ρ_ V).inv ▷ R ≫ (V ◁ e) ▷ R ≫ c ▷ R := by
      simpa only [Category.assoc] using congrArg (fun t => t ≫ (V ◁ e) ▷ R ≫ c ▷ R) hunit
    _ = ((ρ_ V).inv ≫ V ◁ e ≫ c) ▷ R := by simp only [comp_whiskerRight]
    _ = 𝟙 _ := by rw [hu, id_whiskerRight]

end SerrePositivity.DifferentialGraded
