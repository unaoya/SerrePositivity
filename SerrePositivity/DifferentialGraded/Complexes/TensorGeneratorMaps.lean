module
public import SerrePositivity.DifferentialGraded.Complexes.MapEvaluation

/-! # tensor生成元を指定したmapの合成則 -/
@[expose] public section
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory
variable {A : Type u} [CommRing A]

lemma tensorLeft_generator_map {H J K T Z U : Complex A}
    (i : J ⟶ K) (o : H ⊗ K ⟶ Z) (p : Z ⟶ U) (a : K ⟶ T)
    (j : H ⊗ T ⟶ U) (v : J ⟶ T)
    (ho : o ≫ p = (𝟙 H ⊗ₘ a) ≫ j) (ha : i ≫ a = v) :
    ((H ◁ i) ≫ o) ≫ p = (H ◁ v) ≫ j := by
  rw [Category.assoc, ho, id_tensorHom, ← whiskerLeft_comp_assoc, ha]

lemma tensorRight_generator_map {H J K L T Z U : Complex A}
    (i : H ⊗ J ⟶ K) (o : K ⊗ L ⟶ Z) (p : Z ⟶ U) (a : K ⟶ T)
    (j : T ⊗ L ⟶ U) (v : H ⊗ J ⟶ T)
    (ho : o ≫ p = (a ⊗ₘ 𝟙 L) ≫ j) (ha : i ≫ a = v) :
    ((α_ H J L).inv ≫ (i ▷ L) ≫ o) ≫ p = (α_ H J L).inv ≫ (v ▷ L) ≫ j := by
  simp only [Category.assoc]
  rw [ho, tensorHom_id, ← comp_whiskerRight_assoc, ha]

lemma tensor_associator_balance {H J L X Y T : Complex A}
    (a : H ⊗ J ⟶ X) (b : J ⊗ L ⟶ Y) (i : X ⊗ L ⟶ T) (j : H ⊗ Y ⟶ T)
    (h : (a ▷ L) ≫ i = (α_ H J L).hom ≫ (H ◁ b) ≫ j) :
    (H ◁ b) ≫ j = (α_ H J L).inv ≫ (a ▷ L) ≫ i := by
  rw [h, Iso.inv_hom_id_assoc]

end SerrePositivity.DifferentialGraded
