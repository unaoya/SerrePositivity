module
public import SerrePositivity.InfinityCategories.Stable.FunctorLoopCofiberEvaluation
public import SerrePositivity.InfinityCategories.Stable.IntervalSquareFamily
public import SerrePositivity.InfinityCategories.Stable.PushoutComparisonCorners

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
namespace SerrePositivity.InfinityCategories

/-- 概要：区間族の cofiber の最初の二成分の可逆性から第三成分の可逆性を得る。
方針：元の比較辺の二つの入力角と零角を可逆と判定する。
規約：回転の全族を任意の点ごとの族で代用しない。
使われ方：任意の零角の fiber/cofiber 判定の逆方向。 -/
lemma ZeroTriangle.target_isEquivalencePath_of_source_middle {X : SSet.{u}}
    [Quasicategory X] [HasZeroVertex X] [HasFiniteLimits X]
    (s : X ⟶ loopDiagrams X) (hs : s ≫ loopDiagramEvaluation X 1 1 = 𝟙 X)
    (hΩ : IsQCatEquivalence (s ≫ loopDiagramEvaluation X 0 0))
    (t : ZeroTriangle ((ihom (Δ[1] : SSet.{u})).obj X)) (ht : IsCofiberSequence t)
    (h₀ : IsEquivalencePathVertex (squareVertex t.square 0 0))
    (h₁ : IsEquivalencePathVertex (squareVertex t.square 1 0)) :
    IsEquivalencePathVertex (squareVertex t.square 1 1) := by
  let e := intervalSquareComparisonEdge t.square
  have hi : IsInvertibleEdge e := by
    apply pushoutComparison_isInvertible_of_three_corners
      (t.isCofiber_evaluate_of_loopEquivalence s hs hΩ ht
        (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))
      (t.isCofiber_evaluate_of_loopEquivalence s hs hΩ ht
        (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))
    intro i j hij
    apply (intervalSquareComparisonEdge_isInvertible_evaluate_iff t.square i j).mpr
    rcases hij with rfl | rfl
    · fin_cases j
      · exact h₀
      · exact t.zero_corner.isEquivalencePathVertex
    · fin_cases i
      · exact h₀
      · exact h₁
  have h := hi.map (evaluateFunctorAt
    (squareVertex (𝟙 (Δ[1] ⊗ Δ[1] : SSet.{u})) 1 1))
  exact (intervalSquareComparisonEdge_isInvertible_evaluate_iff t.square 1 1).mp h

end SerrePositivity.InfinityCategories
