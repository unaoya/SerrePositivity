module

public import SerrePositivity.InfinityCategories.F1.DiagonalRelativeEvaluation

/-!
概要：対角相対評価の順序の添字変換との整合性。
方針：path の存在から得る順序を単調写像で写し、混合 Hom の二つの表示を比較する。
規約：添字変換は単射に限らず、退化を表す単調写像も含む。
使われ方：Kerodon Corollary 5.6.0.6、分類関手の単体の面・退化との可換性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

/-- 概要：対角相対評価は単調写像による添字変換と可換。
方針：各 Hom の単体で path が与える順序を使い、順向きの混合 Hom の式を比較する。
規約：二つの図式を同じ単調写像で同時に制限する。
使われ方：Kerodon Corollary 5.6.0.6、底とパラメーターを同時に制限した coherent 単体。 -/
lemma diagonalRelativeEvaluation_reindex {B : SSet.{u}} {J K : Type u}
    [LinearOrder J] [LinearOrder K] (α : J →o K) (A : Kᵒᵖ ⥤ Over B)
    (F : EnrichedFunctor SSet.{u} (SimplicialThickening K) (LeftFibrationObject B)) :
    (SimplicialThickening.functor α).comp SSet (diagonalRelativeEvaluation A F) =
      diagonalRelativeEvaluation (α.toFunctor.op ⋙ A)
        ((SimplicialThickening.functor α).comp SSet F) := by
  refine EnrichedFunctor.ext SSet
    (F := (SimplicialThickening.functor α).comp SSet (diagonalRelativeEvaluation A F))
    (G := diagonalRelativeEvaluation (α.toFunctor.op ⋙ A)
      ((SimplicialThickening.functor α).comp SSet F)) (fun _ ↦ rfl) ?_
  intro i j
  simp only [eqToHom_refl, Category.comp_id]
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro P
  have hij : i.as ≤ j.as := SimplicialThickening.Path.le (P.obj 0)
  change (((SimplicialThickening.functor α).map i j ≫
      diagonalRelativeHom A F ((SimplicialThickening.functor α).obj i)
        ((SimplicialThickening.functor α).obj j)).app n) P =
    (diagonalRelativeHom (α.toFunctor.op ⋙ A)
      ((SimplicialThickening.functor α).comp SSet F) i j).app n P
  erw [diagonalRelativeHom_of_le A F _ _ (α.monotone hij),
    diagonalRelativeHom_of_le _ _ i j hij]
  rfl

end SerrePositivity.InfinityCategories
