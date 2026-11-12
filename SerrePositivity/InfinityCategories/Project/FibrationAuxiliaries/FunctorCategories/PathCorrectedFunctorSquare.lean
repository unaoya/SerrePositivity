module

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.FunctorSquarePathLift

/-!
概要：指定された関手同型の path を保つ、厳密に可換な関手正方形のデータ。
方針：相対 path の持ち上げを選び、元の成分との同型と同値性を回収する。
規約：標的の path は元の関手同型を表す指定の path そのもの。
使われ方：同じ局所 cospan の厳密な pullback 比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories

/-- 元の成分と指定 path を保持した、厳密に可換な正方形。 -/
structure PathCorrectedFunctorSquare {A E B : SSet.{u}}
    [Quasicategory E] [Quasicategory B]
    (q : E ⟶ B) (f : A ⟶ E) (g : A ⟶ B) (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso g (f ≫ q)) where
  map : A ⟶ E
  path : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePath E
  comm : map ≫ q = g
  zero : path ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint E 0 = map
  one : path ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint E 1 = f
  over : path ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathMap q =
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.invertibleFunctorEdgePath (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.edge e) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.edge_isInvertible e)

/-- 相対持ち上げにより、指定された同型の path を保つ厳密な正方形を選ぶ。 -/
def pathCorrectedFunctorSquare {A E B : SSet.{u}}
    [Quasicategory E] [Quasicategory B]
    (q : E ⟶ B) (hq : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting q)
    (f : A ⟶ E) (g : A ⟶ B) (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso g (f ≫ q)) :
    PathCorrectedFunctorSquare q f g e := Classical.choice (by
  obtain ⟨f', L, hc, h0, h1, hP⟩ := _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.exists_functorSquare_strictification q hq f g e
  exact ⟨⟨f', L, hc, h0, h1, hP⟩⟩)

/-- 厳密化した成分は、持ち上げた同じ path によって元の成分と同型。 -/
def PathCorrectedFunctorSquare.componentIso {A E B : SSet.{u}}
    [Quasicategory E] [Quasicategory B] {q : E ⟶ B} {f : A ⟶ E} {g : A ⟶ B}
    {e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso g (f ≫ q)} (s : PathCorrectedFunctorSquare q f g e) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso s.map f := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanEquivalencePath_functorIso s.path
  rw [s.zero, s.one] at h
  exact h

/-- 元の成分が同値なら、同じ path に沿う厳密化した成分も同値。 -/
lemma PathCorrectedFunctorSquare.map_isQCatEquivalence {A E B : SSet.{u}}
    [Quasicategory A] [Quasicategory E] [Quasicategory B]
    {q : E ⟶ B} {f : A ⟶ E} {g : A ⟶ B} {e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso g (f ≫ q)}
    (s : PathCorrectedFunctorSquare q f g e) (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence f) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence s.map := hf.ofFunctorIso s.componentIso.symm

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories
