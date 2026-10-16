module
public import SerrePositivity.DifferentialGraded.Functor.Components

/-! # dg関手による微分と指定収縮元の保存 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.DGFunctor
open CategoryTheory HomologicalComplex
variable (A : Type u) [CommRing A] {D : Type v} {E : Type w}
  [DGCategory A D] [DGCategory A E]

lemma map_differential_element (F : DGFunctor A D E) {x y : D} (n : ℤ)
    (f : GradedHom A x y n) :
    (F.map x y).f (n + 1) (differential A f) =
      differential A ((F.map x y).f n f) := by
  exact (ConcreteCategory.congr_hom ((F.map x y).comm n (n + 1)) f).symm

lemma map_contractingElement (F : DGFunctor A D E) (x : D)
    (h : GradedHom A x x (-1))
    (dh : (homObject A D x x).d (-1) 0 h = (unitElement A x).val) :
    (homObject A E (F.obj x) (F.obj x)).d (-1) 0 ((F.map x x).f (-1) h) =
      (unitElement A (F.obj x)).val := by
  have hc := ConcreteCategory.congr_hom ((F.map x x).comm (-1) 0) h
  change (homObject A E (F.obj x) (F.obj x)).d (-1) 0 ((F.map x x).f (-1) h) =
    (F.map x x).f 0 ((homObject A D x x).d (-1) 0 h) at hc
  rw [dh, map_unitElement] at hc
  exact hc

end SerrePositivity.DifferentialGraded.DGFunctor
