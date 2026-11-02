module

public import SerrePositivity.InfinityCategories.Core.Cocone
public import SerrePositivity.InfinityCategories.Core.FunctorEvaluation
public import SerrePositivity.InfinityCategories.Core.FunctorLimits
public import SerrePositivity.InfinityCategories.Core.Join
public import SerrePositivity.InfinityCategories.Core.FilteredExchange.FunctorCoconeEvaluation
public import SerrePositivity.InfinityCategories.Core.FilteredExchange.FunctorCoconeReindex
public import SerrePositivity.InfinityCategories.Stable.TrivialFibrationCocone

/-!
概要：全評価で保存される指定余錐は、形状制限後も全評価で保存される。
方針：同じ元の像の点での評価に、全余錐の射を厳密に同定する。
規約：対象関手の一般の余極限保存は仮定しない。
使われ方：Ind の全四角形族を錐形状へ制限するときの包含による保存。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 指定関手で保存される点ごとの余極限は、任意の形状制限後も保存される。 -/
lemma reindexFunctorCocone_image_isColimit {J K L X Y : SSet.{u}}
    {p : J ⟶ (ihom K).obj X} (c : JoinCocone p) (F : X ⟶ Y)
    (h : ∀ k, IsColimitCone (mapJoinCocone F (evaluateFunctorCocone c k)))
    (f : L ⟶ K) (l : L _⦋0⦌) :
    IsColimitCone (mapJoinCocone F
      (evaluateFunctorCocone (reindexFunctorCocone c f) l)) := by
  apply (isColimitCone_iff_of_coconeMap_eq _ _ ?_).mpr
    (h (f.app (Opposite.op ⦋0⦌) l))
  change ((c.val ≫ (pre f).app X) ≫ evaluateFunctorAt l) ≫ F =
    (c.val ≫ evaluateFunctorAt (f.app (Opposite.op ⦋0⦌) l)) ≫ F
  rw [Category.assoc c.val, functorCoconePrecomp_evaluate]

end SerrePositivity.InfinityCategories.F2
