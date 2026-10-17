module
public import SerrePositivity.DifferentialGraded.Endomorphism.GeneratorHomIso

/-! # dg関手の全Hom写像と閉零前後合成の可換性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory
variable {A : Type u} [CommRing A] {C : Type v} {B : Type w}
  [DGCategory A C] [DGCategory A B] (F : DGFunctor A C B)

lemma dgHomMap_precompose {X X' : ClosedCategory A C} (f : X ⟶ X')
    (Y : ClosedCategory A C) :
    eHomWhiskerRight (Complex A) f Y ≫ F.map X Y =
      F.map X' Y ≫ eHomWhiskerRight (Complex A) (F.onClosed.map f) (F.onClosed.obj Y) := by
  dsimp only [eHomWhiskerRight]
  simp only [Category.assoc]
  rw [F.map_comp, whiskerRight_comp_tensorHom_assoc,
    leftUnitor_inv_comp_tensorHom_assoc]
  rfl

lemma dgHomMap_postcompose (X : ClosedCategory A C) {Y Y' : ClosedCategory A C}
    (g : Y ⟶ Y') :
    eHomWhiskerLeft (Complex A) X g ≫ F.map X Y' =
      F.map X Y ≫ eHomWhiskerLeft (Complex A) (F.onClosed.obj X) (F.onClosed.map g) := by
  dsimp only [eHomWhiskerLeft]
  simp only [Category.assoc]
  rw [F.map_comp, whiskerLeft_comp_tensorHom_assoc,
    rightUnitor_inv_comp_tensorHom_assoc]
  rfl

end SerrePositivity.DifferentialGraded
