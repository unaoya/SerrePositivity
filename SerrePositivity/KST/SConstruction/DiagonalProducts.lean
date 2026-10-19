module
public import SerrePositivity.KST.SConstruction.DiagonalReduction
public import Mathlib.CategoryTheory.Monoidal.Cartesian.FunctorCategory

/-! # 対角実現と積の厳密な比較
概要：二重単体集合の積は対角の積と同型で、射対も元の射対に一致する。
方針：各単体次数で同じ順序付き対を使う。
規約：弱同値や Kan 性を仮定しない。使われ方：反復加法性の行から対角への移行。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet

/-- 単体的図式の積の対角は対角の積に厳密に同型。 -/
def diagonalTensorIso (A B : SimplexCategoryᵒᵖ ⥤ SSet.{u}) :
    simplicialDiagonalFunctor.obj (A ⊗ B) ≅
      simplicialDiagonalFunctor.obj A ⊗ simplicialDiagonalFunctor.obj B :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intros; rfl)

/-- 対角と積の比較は元の二つの射の組を保つ。 -/
lemma diagonalTensorIso_pair {D A B : SimplexCategoryᵒᵖ ⥤ SSet.{u}}
    (f : D ⟶ A) (g : D ⟶ B) :
    simplicialDiagonalFunctor.map (CartesianMonoidalCategory.lift f g) ≫
      (diagonalTensorIso A B).hom =
    CartesianMonoidalCategory.lift
      (simplicialDiagonalFunctor.map f) (simplicialDiagonalFunctor.map g) := by
  rfl

end SerrePositivity.KST.SConstruction
