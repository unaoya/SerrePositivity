module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.AlternatingPresentationDiagrams
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SequentialAlternatingPoints
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.TerminalValuedDiagramComparison

/-!
概要：全交互可算図式の奇数部分列を元の固定標的の定値図式と全関手同型で比較する。
方針：全有限段で挿入点が恒等錐であることから、奇数部分列は全関手圏の終対象となる。
規約：全 FunctorIso を構成し、頂点同型の族だけで代用しない。
使われ方：固定標的 fiber の可算交互余極限の比較。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories


/-- 概要：元の奇数自然数列は単調。
方針：自然数の線形算術。
規約：元の可算添字を使う。
使われ方：奇数部分列の全 nerve 関手。 -/
lemma alternatingOdd_monotone : Monotone (fun n : ℕ ↦ 2 * n + 1) := by
  intro n m h
  change 2 * n + 1 ≤ 2 * m + 1
  omega

variable {μ : Cardinal.{u}} [Fact μ.IsRegular] (hμ : Cardinal.aleph0 < μ)
  {I : SSet.{u}} [Quasicategory I] [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered μ I]
  {B : SSet.{u + 1}} [Quasicategory B]
  (D : (SSet.uliftFunctor.{u + 1, u}).obj I ⟶ B)
  (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone D) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c)
  (hD : ∀ i : I _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ (D.app _ (ULift.up i)))
  (hv : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ c.vertex)
  (i : I _⦋0⦌)
  (H : nerve (ULift.{u + 1} ℕ) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (SSet.yonedaEquiv.symm c.vertex))
  (hH : ∀ n, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveInitialSimplex (2 * n) ≫ H =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.alternatingPresentationTower hμ D c hc hD hv i n).sliceDiagram)

include hH

/-- 概要：貼り合わせた全図式の各奇数頂点は元の恒等錐そのもの。
方針：一つ後の全有限段の比較を、厳密に同定した挿入点へ適用する。
規約：固定標的 slice の実頂点の等式。
使われ方：全奇数部分列の終対象性。 -/
lemma alternatingPresentation_odd_vertex (n : ℕ) :
    H.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (ULift.up (2 * n + 1) : ULift.{u + 1} ℕ)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.sliceIdentityCone c.vertex := by
  have h := congrArg (fun f ↦ SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.alternatingInsertedPoint n ≫ f)) (hH (n + 1))
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.alternatingInsertedPoint_initialSimplex, SSet.yonedaEquiv_comp,
    Equiv.apply_symm_apply] at h
  change _ = SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.alternatingInsertedPoint n ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.alternatingPresentationSuccessorChoice hμ D c hc hD hv
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.alternatingPresentationTower hμ D c hc hD hv i n)).next.sliceDiagram) at h
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.AlternatingPresentationSuccessor.next_inserted_vertex] at h
  exact h

/-- 概要：全奇数部分列は各頂点で終対象。
方針：可算 nerve の任意の零単体を元の自然数として回収する。
規約：点ごとの条件は次の全関手同型の構成入力。
使われ方：全関手圏の終対象性の境界充填。 -/
lemma alternatingPresentation_odd_pointwise_terminal
    (k : (nerve (ULift.{u + 1} ℕ)) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex ((nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialSubsequenceFunctor.{u + 1}
      (fun n ↦ 2 * n + 1) alternatingOdd_monotone) ≫ H).app (Opposite.op ⦋0⦌) k) := by
  have hk : (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialSubsequenceFunctor.{u + 1}
      (fun n ↦ 2 * n + 1) alternatingOdd_monotone)).app (Opposite.op ⦋0⦌) k =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (ULift.up (2 * (k.obj 0).down + 1) : ULift.{u + 1} ℕ) := by
    exact ComposableArrows.ext (fun j ↦ by
      have hj : j = 0 := Fin.eq_zero j
      subst j
      rfl) (fun _ _ ↦ Subsingleton.elim _ _)
  have ht : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex (H.app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (ULift.up (2 * (k.obj 0).down + 1) : ULift.{u + 1} ℕ))) := by
    rw [alternatingPresentation_odd_vertex hμ D c hc hD hv i H hH]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.sliceIdentityCone_isTerminalVertex _
  exact (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex (congrArg (H.app (Opposite.op ⦋0⦌)) hk)).mpr ht

/-- 概要：全奇数部分列と元の恒等錐の定値図式の間の全関手同型。
方針：点ごとの終対象から全関手圏の終対象を構成し、その一意性を使う。
規約：可逆二胞体 FunctorIso を返す。
使われ方：奇数部分列の余極限を元の固定標的と比較する。 -/
def alternatingPresentation_oddSubsequenceIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialSubsequenceFunctor.{u + 1}
      (fun n ↦ 2 * n + 1) alternatingOdd_monotone) ≫ H)
      (SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.sliceIdentityCone c.vertex)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.terminalValuedDiagramConstantIso _
    (alternatingPresentation_odd_pointwise_terminal hμ D c hc hD hv i H hH)
    _ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.sliceIdentityCone_isTerminalVertex _)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
