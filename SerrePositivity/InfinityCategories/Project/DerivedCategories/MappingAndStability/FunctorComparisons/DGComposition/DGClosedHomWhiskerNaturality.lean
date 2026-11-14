module
public import SerrePositivity.DifferentialGraded.Functor.QuasiEquivalence
public import Mathlib.CategoryTheory.Enriched.Ordinary.Basic

/-! # dg 関手と閉零射による豊穣 Hom の前後合成

概要：dg 関手の全 Hom 鎖写像は、指定閉零射による前後合成と厳密に可換。
方針：豊穣合成の保存と単位テンソルの自然性を使う。
規約：元と標的の対象宇宙は独立。使われ方：実 Ore 細分の係数図式の厳密な自然性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory MonoidalCategory DifferentialGraded
variable {A : Type u} [CommRing A] {D : Type v} {E : Type w}
variable [DGCategory A D] [DGCategory A E] (F : DGFunctor A D E)

/-- dg 関手による全 Hom 写像と、閉零射による豊穣前合成の自然性。 -/
lemma dgFunctorHom_precompose {x x' : ClosedCategory A D} (s : x ⟶ x')
    (y : ClosedCategory A D) :
    eHomWhiskerRight (Complex A) s y ≫ F.map x y =
      F.map x' y ≫ eHomWhiskerRight (Complex A) (F.onClosed.map s) (F.onClosed.obj y) := by
  dsimp only [eHomWhiskerRight]
  simp only [Category.assoc]
  rw [F.map_comp, whiskerRight_comp_tensorHom_assoc, leftUnitor_inv_comp_tensorHom_assoc]
  rfl

/-- dg 関手による全 Hom 写像と、閉零射による豊穣後合成の自然性。 -/
lemma dgFunctorHom_postcompose (x : ClosedCategory A D) {y y' : ClosedCategory A D}
    (s : y ⟶ y') :
    eHomWhiskerLeft (Complex A) x s ≫ F.map x y' =
      F.map x y ≫ eHomWhiskerLeft (Complex A) (F.onClosed.obj x) (F.onClosed.map s) := by
  dsimp only [eHomWhiskerLeft]
  simp only [Category.assoc]
  rw [F.map_comp, whiskerLeft_comp_tensorHom_assoc, rightUnitor_inv_comp_tensorHom_assoc]
  rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories
