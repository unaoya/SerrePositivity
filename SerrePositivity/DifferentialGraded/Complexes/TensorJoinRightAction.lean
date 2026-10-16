module
public import SerrePositivity.DifferentialGraded.Complexes.TensorJoinAssociativity

/-! # 前方二因子の合成と後方二因子への作用の交換 -/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory
variable {A : Type u} [CommRing A]

lemma tensorJoin_right_action (U V W T R S : Complex A) (c : U ⊗ V ⟶ W) (r : T ⊗ R ⟶ S) :
    ((α_ U V T).inv ≫ c ▷ T) ▷ R ≫ (α_ W T R).hom ≫ W ◁ r =
    (α_ U (V ⊗ T) R).hom ≫ U ◁ ((α_ V T R).hom ≫ V ◁ r) ≫
      (α_ U V S).inv ≫ c ▷ S := by
  have hα : (α_ U V T).inv ▷ R ≫ (α_ (U ⊗ V) T R).hom =
      (α_ U (V ⊗ T) R).hom ≫ U ◁ (α_ V T R).hom ≫ (α_ U V (T ⊗ R)).inv := by
    monoidal
  rw [comp_whiskerRight, Category.assoc, associator_naturality_left_assoc,
    ← whisker_exchange]
  simp only [whiskerLeft_comp, Category.assoc, associator_inv_naturality_right_assoc]
  simpa only [Category.assoc] using congrArg (fun f => f ≫ (U ⊗ V) ◁ r ≫ c ▷ S) hα

end SerrePositivity.DifferentialGraded
