module

public import SerrePositivity.InfinityCategories.F2.Presentable.AlternatingPresentationDiagrams
public import SerrePositivity.InfinityCategories.F2.Presentable.SequentialAlternatingPoints
public import SerrePositivity.InfinityCategories.F2.Presentable.TerminalValuedDiagramComparison

/-!
概要：全交互可算図式の奇数部分列を元の固定標的の定値図式と全関手同型で比較する。
方針：全有限段で挿入点が恒等錐であることから、奇数部分列は全関手圏の終対象となる。
規約：全 FunctorIso を構成し、頂点同型の族だけで代用しない。
使われ方：固定標的 fiber の可算交互余極限の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable
open HomotopyLimits

/-- 概要：元の奇数自然数列は単調。
方針：自然数の線形算術。
規約：元の可算添字を使う。
使われ方：奇数部分列の全 nerve 関手。 -/
lemma alternatingOdd_monotone : Monotone (fun n : ℕ ↦ 2 * n + 1) := by
  intro n m h
  change 2 * n + 1 ≤ 2 * m + 1
  omega

variable {μ : Cardinal.{u}} [Fact μ.IsRegular] (hμ : Cardinal.aleph0 < μ)
  {I : SSet.{u}} [Quasicategory I] [IsKappaFiltered μ I]
  {B : SSet.{u + 1}} [Quasicategory B]
  (D : (SSet.uliftFunctor.{u + 1, u}).obj I ⟶ B)
  (c : JoinCocone D) (hc : IsColimitCone c)
  (hD : ∀ i : I _⦋0⦌, Compact.IsKappaCompact.{u, u + 1} μ (D.app _ (ULift.up i)))
  (hv : Compact.IsKappaCompact.{u, u + 1} μ c.vertex)
  (i : I _⦋0⦌)
  (H : nerve (ULift.{u + 1} ℕ) ⟶ sliceOver (SSet.yonedaEquiv.symm c.vertex))
  (hH : ∀ n, sequentialNerveInitialSimplex (2 * n) ≫ H =
    (alternatingPresentationTower hμ D c hc hD hv i n).sliceDiagram)

include hH

/-- 概要：貼り合わせた全図式の各奇数頂点は元の恒等錐そのもの。
方針：一つ後の全有限段の比較を、厳密に同定した挿入点へ適用する。
規約：固定標的 slice の実頂点の等式。
使われ方：全奇数部分列の終対象性。 -/
lemma alternatingPresentation_odd_vertex (n : ℕ) :
    H.app (Opposite.op ⦋0⦌) (nerveVertex (ULift.up (2 * n + 1) : ULift.{u + 1} ℕ)) =
      sliceIdentityCone c.vertex := by
  have h := congrArg (fun f ↦ SSet.yonedaEquiv (alternatingInsertedPoint n ≫ f)) (hH (n + 1))
  rw [← Category.assoc, alternatingInsertedPoint_initialSimplex, SSet.yonedaEquiv_comp,
    Equiv.apply_symm_apply] at h
  change _ = SSet.yonedaEquiv (alternatingInsertedPoint n ≫
    (alternatingPresentationSuccessorChoice hμ D c hc hD hv
      (alternatingPresentationTower hμ D c hc hD hv i n)).next.sliceDiagram) at h
  rw [AlternatingPresentationSuccessor.next_inserted_vertex] at h
  exact h

/-- 概要：全奇数部分列は各頂点で終対象。
方針：可算 nerve の任意の零単体を元の自然数として回収する。
規約：点ごとの条件は次の全関手同型の構成入力。
使われ方：全関手圏の終対象性の境界充填。 -/
lemma alternatingPresentation_odd_pointwise_terminal
    (k : (nerve (ULift.{u + 1} ℕ)) _⦋0⦌) :
    IsTerminalVertex ((nerveMap (sequentialSubsequenceFunctor.{u + 1}
      (fun n ↦ 2 * n + 1) alternatingOdd_monotone) ≫ H).app (Opposite.op ⦋0⦌) k) := by
  have hk : (nerveMap (sequentialSubsequenceFunctor.{u + 1}
      (fun n ↦ 2 * n + 1) alternatingOdd_monotone)).app (Opposite.op ⦋0⦌) k =
      nerveVertex (ULift.up (2 * (k.obj 0).down + 1) : ULift.{u + 1} ℕ) := by
    exact ComposableArrows.ext (fun j ↦ by
      have hj : j = 0 := Fin.eq_zero j
      subst j
      rfl) (fun _ _ ↦ Subsingleton.elim _ _)
  have ht : IsTerminalVertex (H.app (Opposite.op ⦋0⦌)
      (nerveVertex (ULift.up (2 * (k.obj 0).down + 1) : ULift.{u + 1} ℕ))) := by
    rw [alternatingPresentation_odd_vertex hμ D c hc hD hv i H hH]
    exact F1B.sliceIdentityCone_isTerminalVertex _
  exact (congrArg IsTerminalVertex (congrArg (H.app (Opposite.op ⦋0⦌)) hk)).mpr ht

/-- 概要：全奇数部分列と元の恒等錐の定値図式の間の全関手同型。
方針：点ごとの終対象から全関手圏の終対象を構成し、その一意性を使う。
規約：可逆二胞体 FunctorIso を返す。
使われ方：奇数部分列の余極限を元の固定標的と比較する。 -/
def alternatingPresentation_oddSubsequenceIso :
    FunctorIso (nerveMap (sequentialSubsequenceFunctor.{u + 1}
      (fun n ↦ 2 * n + 1) alternatingOdd_monotone) ≫ H)
      (SSet.const (sliceIdentityCone c.vertex)) :=
  terminalValuedDiagramConstantIso _
    (alternatingPresentation_odd_pointwise_terminal hμ D c hc hD hv i H hH)
    _ (F1B.sliceIdentityCone_isTerminalVertex _)

end SerrePositivity.InfinityCategories.F2.Presentable
