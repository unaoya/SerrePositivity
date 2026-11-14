module
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.Algebra.Homology.Additive

/-!
概要：複体値の図式と、図式圏における複体の交換。
方針：対象と微分を同じ添字で評価し、Mathlib の asFunctor と互いに戻す。
規約：複体の形・図式の圏に制限を置かない。射も同じ成分を保持する。
使われ方：HA 1.2.4、G10 の線形重みから図式への Hom 複体。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w t r
open CategoryTheory CategoryTheory.Limits
namespace SerrePositivity.HomologicalAlgebra
variable (J : Type u) [Category.{v} J] (C : Type w) [Category.{t} C] [HasZeroMorphisms C]
variable {ι : Type r} (c : ComplexShape ι)

/-- 複体値の図式を、同じ成分を持つ図式圏の複体へ交換する全関手。 -/
def functorToComplexOfFunctors :
    (J ⥤ HomologicalComplex C c) ⥤ HomologicalComplex (J ⥤ C) c where
  obj F :=
    { X := fun n => F ⋙ HomologicalComplex.eval C c n
      d := fun n m =>
        { app := fun j => (F.obj j).d n m
          naturality _ _ f := (F.map f).comm n m }
      shape := by
        intro n m h
        apply NatTrans.ext
        funext j
        exact (F.obj j).shape n m h
      d_comp_d' := by
        intro n m k _ _
        apply NatTrans.ext
        funext j
        exact (F.obj j).d_comp_d n m k }
  map f :=
    { f := fun n => Functor.whiskerRight f (HomologicalComplex.eval C c n)
      comm' := by
        intro n m _
        apply NatTrans.ext
        funext j
        exact (f.app j).comm n m }
  map_id F := by rfl
  map_comp f g := by rfl

/-- 交換して各図式対象で評価すると元の複体に戻る。 -/
def functorComplexExchangeUnitIso :
    𝟭 (J ⥤ HomologicalComplex C c) ≅
      functorToComplexOfFunctors J C c ⋙ HomologicalComplex.complexOfFunctorsToFunctorToComplex :=
  NatIso.ofComponents (fun F => NatIso.ofComponents (fun j =>
    HomologicalComplex.Hom.isoOfComponents (fun n => Iso.refl _) (by intros; simp; rfl))
    (by intros; ext n; simp; rfl)) (by intros; ext j n; simp; rfl)

/-- 各対象へ評価した後で交換すると元の図式複体に戻る。 -/
def functorComplexExchangeCounitIso :
    HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙ functorToComplexOfFunctors J C c ≅
      𝟭 (HomologicalComplex (J ⥤ C) c) :=
  NatIso.ofComponents (fun F => HomologicalComplex.Hom.isoOfComponents
    (fun n => NatIso.ofComponents (fun j => Iso.refl _) (by intros; simp; rfl))
    (by intros; ext j; simp; rfl)) (by intros; ext n j; simp; rfl)

end SerrePositivity.HomologicalAlgebra
