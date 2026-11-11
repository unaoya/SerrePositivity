module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IntervalFunctorHomPrism
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.FunctorPrismFamilyCurry

/-!
概要：両端の図式を固定した prism を、元の関手圏の区間 Hom の族へ戻す。
方針：同じ prism を curry し、両端条件を内部 Hom の端点条件に移す。
規約：二方向の往復は全パラメーターで厳密な等式。
使われ方：分類先の固定成分 fiber の三辺固定の表示。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 両端で元の二つの図式に定値な prism を、同じ関手圏の区間 Hom に戻す。 -/
def intervalFunctorHomPrismCurry {T B X : SSet.{u}} {F G : B ⟶ X}
    (H : ((Δ[1] : SSet.{u}) ⊗ B) ⊗ T ⟶ X)
    (h₀ : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 B ▷ T) ≫ H = fst B T ≫ F)
    (h₁ : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 B ▷ T) ≫ H = fst B T ≫ G) :
    T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingCurryOfEndpoints (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.functorParameterizedCurry H)
    (by
      apply uncurry_injective
      change uncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.simplexPrismVertex 1 0 T ≫ _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.functorParameterizedCurry H) = _
      rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.functorParameterizedPrism_vertex, _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.functorParameterizedPrism_curry]
      change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 B ▷ T) ≫ H = uncurry (SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F))
      rw [h₀, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.uncurry_const_functorVertex])
    (by
      apply uncurry_injective
      change uncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.simplexPrismVertex 1 1 T ≫ _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.functorParameterizedCurry H) = _
      rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.functorParameterizedPrism_vertex, _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.functorParameterizedPrism_curry]
      change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 B ▷ T) ≫ H = uncurry (SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G))
      rw [h₁, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.uncurry_const_functorVertex])

/-- 同じ両端固定の prism を Hom に戻して評価すると、元の prism を厳密に回収する。 -/
lemma intervalFunctorHomPrism_curry {T B X : SSet.{u}} {F G : B ⟶ X}
    (H : ((Δ[1] : SSet.{u}) ⊗ B) ⊗ T ⟶ X)
    (h₀ : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 B ▷ T) ≫ H = fst B T ≫ F)
    (h₁ : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 B ▷ T) ≫ H = fst B T ≫ G) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalFunctorHomPrism (intervalFunctorHomPrismCurry H h₀ h₁) = H := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalFunctorHomPrism intervalFunctorHomPrismCurry
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_curryOfEndpoints, _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.functorParameterizedPrism_curry]

/-- 元の区間 Hom の全パラメーターの族を展開して戻すと、元の族を厳密に回収する。 -/
lemma intervalFunctorHomPrismCurry_prism {T B X : SSet.{u}} {F G : B ⟶ X}
    (f : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G)) :
    intervalFunctorHomPrismCurry (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalFunctorHomPrism f)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalFunctorHomPrism_zero f) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalFunctorHomPrism_one f) = f := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalFunctorHomPrism_injective F G
  exact intervalFunctorHomPrism_curry _ _ _

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
