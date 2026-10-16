module
public import SerrePositivity.DifferentialGraded.Complexes.TensorJoinHomNaturality
public import Mathlib.Tactic.CategoryTheory.Monoidal.Basic

/-! # 前方tensor因子の合成と残る右因子の結合則 -/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory
variable {A : Type u} [CommRing A]

/-- 結合的な前方合成に右因子を残す操作も結合則を保つ。 -/
lemma tensorJoin_assoc (U V T W X Z R : Complex A)
    (f : U ⊗ V ⟶ W) (g : V ⊗ T ⟶ X) (h : W ⊗ T ⟶ Z) (k : U ⊗ X ⟶ Z)
    (ha : (f ▷ T) ≫ h = (α_ U V T).hom ≫ U ◁ g ≫ k) :
    (f ▷ (T ⊗ R)) ≫ (α_ W T R).inv ≫ h ▷ R =
    (α_ U V (T ⊗ R)).hom ≫ U ◁ ((α_ V T R).inv ≫ g ▷ R) ≫
      (α_ U X R).inv ≫ k ▷ R := by
  have hα : (α_ (U ⊗ V) T R).inv ≫ (α_ U V T).hom ▷ R =
      (α_ U V (T ⊗ R)).hom ≫ U ◁ (α_ V T R).inv ≫ (α_ U (V ⊗ T) R).inv := by
    monoidal
  rw [associator_inv_naturality_left_assoc, ← comp_whiskerRight, ha]
  simp only [comp_whiskerRight, whiskerLeft_comp, Category.assoc]
  simp only [associator_inv_naturality_middle_assoc]
  simpa only [Category.assoc] using
    congrArg (fun t => t ≫ (U ◁ g) ▷ R ≫ k ▷ R) hα

end SerrePositivity.DifferentialGraded
