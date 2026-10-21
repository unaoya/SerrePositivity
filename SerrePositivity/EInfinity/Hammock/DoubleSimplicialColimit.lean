module

public import SerrePositivity.EInfinity.Hammock.DoubleSimplicialDiagonal
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory

/-!
# 元の全語の余極限と対角の交換

概要：元の全単体・標準射を保持して同じ比較を余極限へ渡す。
方針：元の点ごとの包含と交わり、同じ余極限余錐の普遍性を使う。
規約：全語の添字の filtered 性は仮定しない。
使われ方：DK5.7の元の左 hammock 比較の弱同値性。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.EInfinity.Hammock.DoubleSimplicial
open CategoryTheory CategoryTheory.Limits
variable {I : Type} [SmallCategory I]
instance diagonal_preservesColimitsOfShape :
    PreservesColimitsOfShape I (diagonalFunctor : SimplicialObject SSet.{u} ⥤ SSet.{u}) := by
  have : PreservesColimitsOfShape I
      (Functor.uncurry : (SimplexCategoryᵒᵖ ⥤ SimplexCategoryᵒᵖ ⥤ Type u) ⥤
        SimplexCategoryᵒᵖ × SimplexCategoryᵒᵖ ⥤ Type u) := by
    change PreservesColimitsOfShape I (Functor.currying (C := SimplexCategoryᵒᵖ) (D :=
      SimplexCategoryᵒᵖ)
      (E := Type u)).functor
    infer_instance
  dsimp only [diagonalFunctor]
  infer_instance
def diagonalPointwiseIsColimit (F : I ⥤ SimplicialObject SSet.{u}) :
    IsColimit (diagonalFunctor.mapCocone (pointwiseCocone F)) :=
  isColimitOfPreserves diagonalFunctor (pointwiseIsColimit F)
def diagonalColimitIso (F : I ⥤ SimplicialObject SSet.{u}) :
    colimit (F ⋙ diagonalFunctor) ≅ diagonalFunctor.obj (F.flip ⋙ colim) :=
  (colimit.isColimit (F ⋙ diagonalFunctor)).coconePointUniqueUpToIso
    (diagonalPointwiseIsColimit F)
lemma diagonalColimitIso_ι (F : I ⥤ SimplicialObject SSet.{u}) (i : I) :
    colimit.ι (F ⋙ diagonalFunctor) i ≫ (diagonalColimitIso F).hom =
      diagonalFunctor.map ((pointwiseCocone F).ι.app i) := by
  exact IsColimit.comp_coconePointUniqueUpToIso_hom
    (colimit.isColimit (F ⋙ diagonalFunctor)) (diagonalPointwiseIsColimit F) i
end SerrePositivity.EInfinity.Hammock.DoubleSimplicial
