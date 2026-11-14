module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.FunctorLoopCofiberEvaluation
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IntervalSquareFamily
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.PushoutComparisonCorners

/-!
概要：cofiber の区間族で最初の二成分が可逆なら第三成分も可逆である。
方針：区間族を実四角形の比較辺に読み戻し、入力 span の三角で検出する。
規約：一般安定性や有限余極限を仮定しない。
使われ方：回転した cofiber 比較から懸垂の比較の可逆性を導く。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：区間族の cofiber の最初の二成分の可逆性から第三成分の可逆性を得る。
方針：元の比較辺の二つの入力角と零角を可逆と判定する。
規約：回転の全族を任意の点ごとの族で代用しない。
使われ方：任意の零角の fiber/cofiber 判定の逆方向。 -/
lemma ZeroTriangle.target_isEquivalencePath_of_source_middle {X : SSet.{u}}
    [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.HasZeroVertex X] [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteLimits X]
    (s : X ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagrams X) (hs : s ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 1 1 = 𝟙 X)
    (hΩ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (s ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 0 0))
    (t : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroTriangle ((ihom (Δ[1] : SSet.{u})).obj X)) (ht : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsCofiberSequence t)
    (h₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsEquivalencePathVertex (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex t.square 0 0))
    (h₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsEquivalencePathVertex (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex t.square 1 0)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsEquivalencePathVertex (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex t.square 1 1) := by
  let e := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.intervalSquareComparisonEdge t.square
  have hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge e := by
    apply _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pushoutComparison_isInvertible_of_three_corners
      (t.isCofiber_evaluate_of_loopEquivalence s hs hΩ ht
        (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))
      (t.isCofiber_evaluate_of_loopEquivalence s hs hΩ ht
        (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))
    intro i j hij
    apply (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.intervalSquareComparisonEdge_isInvertible_evaluate_iff t.square i j).mpr
    rcases hij with rfl | rfl
    · fin_cases j
      · exact h₀
      · exact t.zero_corner.isEquivalencePathVertex
    · fin_cases i
      · exact h₀
      · exact h₁
  have h := hi.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (𝟙 (Δ[1] ⊗ Δ[1] : SSet.{u})) 1 1))
  exact (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.intervalSquareComparisonEdge_isInvertible_evaluate_iff t.square 1 1).mp h

with_weak_namespace _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroTriangle export _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroTriangle (target_isEquivalencePath_of_source_middle)


end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
