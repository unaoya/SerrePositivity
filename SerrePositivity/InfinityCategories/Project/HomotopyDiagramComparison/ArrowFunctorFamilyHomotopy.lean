module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalencePath
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingSpaceIntervalVertices

/-!
概要：矢印関手の元の族を、その両端評価を結ぶ円柱へ移す。
方針：元の族を uncurry し、各指定辺を元の点で評価して回収する。
規約：元の族・元の点・指定辺の全一単体を保持。充填性は不要。
使われ方：矢印関手圏内の全錐を、元の二つの全錐の比較円柱にする。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison

/-- 元の矢印関手の族を、その両端評価を結ぶ同じ円柱として保持する。 -/
def arrowFunctorFamilyHomotopy {A X : SSet.{u}}
    (F : A ⟶ (ihom (Δ[1] : SSet.{u})).obj X) :
    SSet.Homotopy (F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))
      (F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) where
  h := (β_ A (Δ[1] : SSet.{u})).hom ≫ uncurry F
  h₀ := by
    rw [← Category.assoc]
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 A ≫ uncurry F = _
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.curry_evaluateFunctorAt_interval, curry_uncurry]
    rfl
  h₁ := by
    rw [← Category.assoc]
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 A ≫ uncurry F = _
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.curry_evaluateFunctorAt_interval, curry_uncurry]
    rfl
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    exact False.elim s.1.property

/-- 元の族が指定点で元の辺を表すなら、円柱の同じ点の辺は元の全一単体そのもの。 -/
lemma arrowFunctorFamilyHomotopy_vertex {A X : SSet.{u}}
    (F : A ⟶ (ihom (Δ[1] : SSet.{u})).obj X) (a : A _⦋0⦌)
    {x y : X _⦋0⦌} (e : SSet.Edge x y)
    (ha : F.app (Opposite.op ⦋0⦌) a = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.yonedaEquiv.symm e.edge)) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (arrowFunctorFamilyHomotopy F) a).edge = e.edge := by
  have hp : SSet.yonedaEquiv.symm a ≫ F =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.yonedaEquiv.symm e.edge)) := by
    rw [SSet.yonedaEquiv_symm_comp, ha]
  have H : (SSet.yonedaEquiv.symm a ▷ (Δ[1] : SSet.{u})) ≫
      (arrowFunctorFamilyHomotopy F).h =
        snd (Δ[0] : SSet.{u}) Δ[1] ≫ SSet.yonedaEquiv.symm e.edge := by
    rw [arrowFunctorFamilyHomotopy, ← Category.assoc,
      BraidedCategory.braiding_naturality_left, Category.assoc,
      ← uncurry_natural_left, hp, SSet.yonedaEquiv_symm_zero, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.uncurry_const_functorVertex,
      ← Category.assoc]
    rfl
  rw [SSet.yonedaEquiv_symm_zero] at H
  have hh := congrArg (fun f => f.app (Opposite.op ⦋1⦌)
    ((SSet.Truncated.Edge.id (X := (truncation 2).obj (Δ[0] : SSet.{u}))
      (stdSimplex.obj₀Equiv.symm 0)).edge, _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge)) H
  have hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge = SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})) := by
    apply stdSimplex.ext
    intro j
    fin_cases j <;> rfl
  calc
    _ = (SSet.yonedaEquiv.symm e.edge).app (Opposite.op ⦋1⦌)
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge := by
      change (arrowFunctorFamilyHomotopy F).h.app (Opposite.op ⦋1⦌)
        ((SSet.Truncated.Edge.id (X := (truncation 2).obj A) a).edge,
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge) = _
      change (arrowFunctorFamilyHomotopy F).h.app (Opposite.op ⦋1⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant a 1, _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge) =
        (SSet.yonedaEquiv.symm e.edge).app (Opposite.op ⦋1⦌) _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge at hh
      simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_one] using hh
    _ = e.edge := by
      rw [hi]
      change SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u}) ≫ SSet.yonedaEquiv.symm e.edge) = _
      rw [Category.id_comp, Equiv.apply_symm_apply]

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
