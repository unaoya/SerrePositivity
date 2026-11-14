module

public import SerrePositivity.KST.LocalizingInvariants.SimplexTerminalPullbackFamily
public import SerrePositivity.KST.LocalizingInvariants.VerdierSimplexDenominators

/-!
概要：有限線型図式の終端を Verdier 分母で置換し、同じ全図式の弱同値を構成する。
方針：終端で列四角形を固定した相対 pullback 族を転置し、全点の分母条件を回収する。
規約：共有終端の四角形を厳密に保持する。商図式の全持ち上げや c5 完成はまだ主張しない。
使われ方：c5 の長さに関する帰納法で、前段全体を同時に精密化する工程。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.Fibration
namespace SerrePositivity.KST.LocalizingInvariants

/-- 同じ全 pullback 四角形族を、全図式圏における四角形へ移す。 -/
def terminalRefinementSquare {X : SSet.{u}} {n : ℕ}
    (F : (Δ[n] : SSet.{u}) ⟶ pullbackDiagrams X) :
    (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ (ihom (Δ[n] : SSet.{u})).obj X :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv Δ[n] (Δ[1] ⊗ Δ[1]) X
    (F ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ IsPullbackDiagramVertex).ι)

private lemma terminalFlip_evaluate {A K X : SSet.{u}}
    (F : A ⟶ (ihom K).obj X) (a : A _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv A K X F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt a =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv K X).symm (F.app (Opposite.op ⦋0⦌) a) := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.internalHomFlipHomEquiv_app_zero (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv A K X F) a
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv K A X (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv A K X F) = F :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv A K X).symm_apply_apply F
  rw [he] at h
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex_injective
  rw [← h]
  exact ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv K X).apply_symm_apply _).symm

/-- 全図式の四角形の各評価は、元の同じ普遍四角形そのもの。 -/
lemma terminalRefinementSquare_evaluate {X : SSet.{u}} {n : ℕ}
    (F : (Δ[n] : SSet.{u}) ⟶ pullbackDiagrams X) (k : (Δ[n] : SSet.{u}) _⦋0⦌) :
    terminalRefinementSquare F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt k =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ _).symm (F.app (Opposite.op ⦋0⦌) k).val :=
  terminalFlip_evaluate _ k

/-- 元の安定圏の有限極限から、転置した全図式の四角形の普遍性を証明する。 -/
lemma terminalRefinementSquare_isPullback {B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {n : ℕ}
    (F : (Δ[n] : SSet.{u}) ⟶ pullbackDiagrams B.obj) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (terminalRefinementSquare F) := by
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteLimits B.obj := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.hasFiniteLimits_of_isStable B.obj
  apply (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isPullbackSquare_functor_iff _).mpr
  intro k
  rw [terminalRefinementSquare_evaluate]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex (F.app (Opposite.op ⦋0⦌) k)

section
variable {X : SSet.{u}} {n : ℕ} (D : (Δ[n] : SSet.{u}) ⟶ X)
  (s : (Δ[1] : SSet.{u}) ⟶ X)
  (hs : s.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
    D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n)))
  (F : (Δ[n] : SSet.{u}) ⟶ pullbackDiagrams X)
  (hF : F ≫ pullbackProjection X = _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.simplexTerminalCospanFamily D s hs)

include hF

/-- 全図式の右辺は指定辺の定値全族を厳密に回収する。 -/
lemma terminalRefinementSquare_right :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ terminalRefinementSquare F =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv Δ[n] Δ[1] X (SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex s)) := by
  unfold terminalRefinementSquare
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv_pre_app]
  apply congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv Δ[n] Δ[1] X)
  have h := congrArg (· ≫ (pre horn₂₂.ι₀₂).app X) hF
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.simplexTerminalCospanFamily_right] at h
  simpa only [pullbackProjection, Category.assoc, ← NatTrans.comp_app, ← pre_map,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.cospanSquareBoundary_rightEdge] using h

/-- 全図式の上辺は元の図式の指定終端辺族を厳密に回収する。 -/
lemma terminalRefinementSquare_top :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ terminalRefinementSquare F =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv Δ[n] Δ[1] X (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.simplexTerminalArrowFamily D) := by
  unfold terminalRefinementSquare
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv_pre_app]
  apply congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv Δ[n] Δ[1] X)
  have h := congrArg (· ≫ (pre horn₂₂.ι₁₂).app X) hF
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.simplexTerminalCospanFamily_top] at h
  simpa only [pullbackProjection, Category.assoc, ← NatTrans.comp_app, ← pre_map,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.cospanSquareBoundary_topEdge] using h

/-- 精密化する前の全図式は四角形の左上角として厳密に回収される。 -/
lemma terminalRefinementSquare_original :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (terminalRefinementSquare F) 0 1 = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex D := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ terminalRefinementSquare F).app (Opposite.op ⦋0⦌)
    (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex D
  rw [terminalRefinementSquare_top D s hs F hF, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.internalHomFlipHomEquiv_app_zero,
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.simplexTerminalArrowFamily_source]

/-- 指定された元の辺を各頂点で厳密に回収する。 -/
lemma terminalRefinementSquare_right_evaluate (k : (Δ[n] : SSet.{u}) _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ terminalRefinementSquare F) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt k = s := by
  rw [terminalRefinementSquare_right D s hs F hF, terminalFlip_evaluate]
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv Δ[1] X).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex s) = s
  exact Equiv.symm_apply_apply _ _

end

/-- 元の全図式を同時に精密化し、共有終端の四角形と元の分母条件を保つ。
終端は指定辺の源に厳密に戻るので、次の辺との貼合せに使える。 -/
lemma exists_verdierSimplexTerminalRefinement {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C} (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q)
    {n : ℕ} (D : (Δ[n] : SSet.{u}) ⟶ B.obj) (s : (Δ[1] : SSet.{u}) ⟶ B.obj)
    (hs : s.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
      D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n)))
    (hW : SSet.yonedaEquiv s ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) :
    ∃ Q : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ (ihom (Δ[n] : SSet.{u})).obj B.obj,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare Q ∧ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex Q 0 1 = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex D ∧
        Q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (Fin.last n)) =
          _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareColumnDiagram s ∧
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareLeftArrow Q).edge ∈
          (relativeFirstRowSimplex q n).obj (Opposite.op ⦋1⦌) := by
  obtain ⟨F, hF, hlast⟩ := exists_simplexTerminalPullbackFamily D s hs
  let Q := terminalRefinementSquare F
  have hQ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare Q := terminalRefinementSquare_isPullback F
  refine ⟨Q, hQ, terminalRefinementSquare_original D s hs F hF, ?_, ?_⟩
  · rw [terminalRefinementSquare_evaluate, hlast]
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ _).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ _
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareColumnDiagram s)) = _
    exact Equiv.symm_apply_apply _ _
  · apply (relativeFirstRowSimplex_pullback_iff h n Q hQ).mpr
    rw [relativeFirstRowSimplex_mem_edge_iff h n]
    intro k
    have hr := terminalRefinementSquare_right_evaluate D s hs F hF k
    have he : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := B.obj) k).app (Opposite.op ⦋1⦌)
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareRightArrow Q).edge = SSet.yonedaEquiv s := by
      rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareRightArrow_edge, ← SSet.yonedaEquiv_comp, hr]
    exact he ▸ hW

end SerrePositivity.KST.LocalizingInvariants
