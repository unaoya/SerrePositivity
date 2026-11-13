module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.Cocone
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FunctorEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.FunctorLimits
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.CoconeComparison.FunctorCoconeEvaluation
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.CoconeComparison.FunctorCoconeReindex
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.TrivialFibrationCocone

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
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange

/-- 指定関手で保存される点ごとの余極限は、任意の形状制限後も保存される。 -/
lemma reindexFunctorCocone_image_isColimit {J K L X Y : SSet.{u}}
    {p : J ⟶ (ihom K).obj X} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) (F : X ⟶ Y)
    (h : ∀ k, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone F (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.evaluateFunctorCocone c k)))
    (f : L ⟶ K) (l : L _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone F
      (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.evaluateFunctorCocone (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.reindexFunctorCocone c f) l)) := by
  apply (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.isColimitCone_iff_of_coconeMap_eq _ _ ?_).mpr
    (h (f.app (Opposite.op ⦋0⦌) l))
  change ((c.val ≫ (pre f).app X) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt l) ≫ F =
    (c.val ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (f.app (Opposite.op ⦋0⦌) l)) ≫ F
  rw [Category.assoc c.val, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.functorCoconePrecomp_evaluate]

end SerrePositivity.InfinityCategories.Project.FilteredExchange
