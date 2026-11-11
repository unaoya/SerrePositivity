module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorHomotopy
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.CoherentColimitCoconeEdge
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.CoherentColimitFunctor
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.CoherentTotalCocone
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoconeFamily

/-!
概要：元の比較円柱を、元の全空間余錐間の全円柱へ持ち上げる。
方針：普遍余錐の切断で写した関手辺を読み戻し、元の図式への制限を照合する。
規約：元の比較円柱は厳密に回収。使われ方：余極限関手の作用と単位の同時比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange
variable (B : SSet.{u})
  {F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}} (H : SSet.Homotopy F G)

/-- 元の全空間余錐間の指定辺を、その二つの全余錐の比較円柱として読む。 -/
def coherentColimitCoconeHomotopy :
    SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalCocone F).val (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalCocone G).val :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyOfFunctorEdge (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentColimitCoconeEdge B H)

/-- 持ち上げた全円柱は、元の関手辺を選んだ切断で写して展開した射そのもの。 -/
lemma coherentColimitCoconeHomotopy_h :
    (coherentColimitCoconeHomotopy B H).h =
      uncurry (curry H.h ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentColimitCoconeFunctor B) := by
  change uncurry (SSet.yonedaEquiv.symm ((_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentColimitCoconeFunctor B).app
    (Opposite.op ⦋1⦌) (SSet.yonedaEquiv (curry H.h)))) = _
  rw [← SSet.yonedaEquiv_comp, Equiv.symm_apply_apply]

/-- 全余錐円柱の curry は、元の円柱の関手辺への切断の作用そのもの。 -/
lemma coherentColimitCoconeHomotopy_curry :
    curry (coherentColimitCoconeHomotopy B H).h =
      curry H.h ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentColimitCoconeFunctor B := by
  rw [coherentColimitCoconeHomotopy_h, curry_uncurry]

/-- 全余錐円柱の元の図式への制限は、元の指定比較円柱そのもの。 -/
lemma coherentColimitCoconeHomotopy_restrict :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl ((SSet.uliftFunctor.{u + 1, u}).obj B) (Δ[0] : SSet.{u + 1}) ▷ Δ[1]) ≫
      (coherentColimitCoconeHomotopy B H).h = H.h := by
  rw [coherentColimitCoconeHomotopy_h, ← uncurry_pre_app]
  change uncurry ((curry H.h ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentColimitCoconeFunctor B) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeRestriction _ _) = H.h
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentColimitCoconeFunctor_restrict, Category.comp_id, uncurry_curry]

end SerrePositivity.InfinityCategories.Project.FilteredExchange
