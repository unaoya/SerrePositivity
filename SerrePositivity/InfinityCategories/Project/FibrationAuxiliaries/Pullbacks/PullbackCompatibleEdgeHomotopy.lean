module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanHomotopyEquivalence
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
概要：像の一次単体が一致する成分辺の全円柱を同じ pullback に貼り合わせる。
方針：関手空間の一次単体の等式を円柱の等式へ移し、両端を二射影で検査する。
規約：元の二射と全パラメーターを保持する。
使われ方：両端固定の代表辺の変更から元の pullback 上の関手同型を作る。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Pullbacks

/-- 成分辺の像の一次単体が一致すれば、同じ二つの円柱の像も一致する。 -/
lemma simplicialHomotopyOfFunctorEdge_comp_eq
    {A X Y Z : SSet.{u}} (f : X ⟶ Z) (g : Y ⟶ Z)
    {a₀ a₁ : A ⟶ X} {b₀ b₁ : A ⟶ Y}
    (l : SSet.Truncated.Edge (X := (truncation 2).obj ((ihom A).obj X))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a₀) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a₁))
    (r : SSet.Truncated.Edge (X := (truncation 2).obj ((ihom A).obj Y))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex b₀) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex b₁))
    (h : ((ihom A).map f).app (Opposite.op ⦋1⦌) l.edge =
      ((ihom A).map g).app (Opposite.op ⦋1⦌) r.edge) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyOfFunctorEdge l).h ≫ f =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyOfFunctorEdge r).h ≫ g := by
  change uncurry (SSet.yonedaEquiv.symm l.edge) ≫ f =
    uncurry (SSet.yonedaEquiv.symm r.edge) ≫ g
  rw [← uncurry_natural_right, ← uncurry_natural_right]
  apply congrArg uncurry
  apply SSet.yonedaEquiv.injective
  rw [SSet.yonedaEquiv_comp, SSet.yonedaEquiv_comp,
    Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  exact h

/-- 整合する成分辺の同じ二円柱は、元の二射を結ぶ pullback の円柱となる。 -/
def pullbackHomotopyOfCompatibleEdges {A X Y Z : SSet.{u}} (f : X ⟶ Z) (g : Y ⟶ Z)
    (a b : A ⟶ pullback f g)
    (l : SSet.Truncated.Edge (X := (truncation 2).obj ((ihom A).obj X))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (a ≫ pullback.fst f g)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (b ≫ pullback.fst f g)))
    (r : SSet.Truncated.Edge (X := (truncation 2).obj ((ihom A).obj Y))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (a ≫ pullback.snd f g)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (b ≫ pullback.snd f g)))
    (h : ((ihom A).map f).app (Opposite.op ⦋1⦌) l.edge =
      ((ihom A).map g).app (Opposite.op ⦋1⦌) r.edge) : SSet.Homotopy a b := by
  let H := pullback.lift (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyOfFunctorEdge l).h
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyOfFunctorEdge r).h (simplicialHomotopyOfFunctorEdge_comp_eq f g l r h)
  refine { h := H, h₀ := ?_, h₁ := ?_, rel := ?_ }
  · apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst]
      exact (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyOfFunctorEdge l).h₀
    · rw [Category.assoc, pullback.lift_snd]
      exact (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyOfFunctorEdge r).h₀
  · apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst]
      exact (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyOfFunctorEdge l).h₁
    · rw [Category.assoc, pullback.lift_snd]
      exact (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyOfFunctorEdge r).h₁
  · apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    exact False.elim s.1.property

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Pullbacks
