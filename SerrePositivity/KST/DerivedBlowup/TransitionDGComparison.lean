module

public import SerrePositivity.KST.DerivedBlowup.ChartBaseChangeDGFunctor
public import SerrePositivity.KST.DerivedBlowup.ChartDGFunctors
public import SerrePositivity.KST.DerivedBlowup.FiniteOverlapTransitions

/-!
概要：KST §3.1 の任意の共通係数環でのチャート dg 底変更比較。
方針：チャート代数射と可逆 pivot 座標を入力にして、底変更と可逆基底変換を合成する。
規約：二重重なりに限定せず、全有限重なりの局所化環にも適用する。
使われ方：全有限 Čech 図式の局所 dg 比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory

variable {R B : Type u} [CommRing R] [CommRing B] [Algebra R B] {r : ℕ}

/-- 概要：規格化した座標とチャート遷移の像は同じ微分を与える。
方針：座標公式を生成元微分の関数へ写す。
規約：KST §3.1。使われ方：底変更 dg 関手の目標の同定。 -/
theorem chartTransitionDifferential_id (a : Fin (r + 1) → R) (i k : Fin (r + 1))
    (f : ChartRing R i →ₐ[R] B) (s : Bˣ) (hs : ↑s = f (chartCoordinate R i k)) :
    (chartKoszulDifferential (fun j => algebraMap R B (a j))
      (normalizeCoordinates (fun j => f (chartCoordinate R i j)) s) k).comp LinearMap.id =
    chartKoszulDifferential (fun j => algebraMap R B (a j))
      (fun j => chartTransition i k f s (chartCoordinate R k j)) k := by
  rw [LinearMap.comp_id]
  congr 1
  funext j
  exact (chartTransition_coordinate i k j f s hs).symm

/-- 概要：遷移環射に沿う底変更を規格化した外積模型へ送る dg 関手。
方針：一般のチャート底変更と恒等生成元での微分同定を合成する。
規約：KST §3.1。使われ方：可逆基底変換の前段。 -/
def chartTransitionNormalizedDGFunctor (a : Fin (r + 1) → R) (i k : Fin (r + 1))
    (f : ChartRing R i →ₐ[R] B) (s : Bˣ) (hs : ↑s = f (chartCoordinate R i k)) :
    EnrichedFunctor (DifferentialGraded.Complex B)
      (DifferentialGraded.ScalarExtension.DGBaseChange (chartTransition i k f s).toRingHom
        (DerivedChartObject a k))
      (ExteriorKoszulObject (chartKoszulDifferential (fun j => algebraMap R B (a j))
        (normalizeCoordinates (fun j => f (chartCoordinate R i j)) s) k)) :=
  EnrichedFunctor.comp (DifferentialGraded.Complex B)
    (chartBaseChangeDGFunctor a k (chartTransition i k f s))
    (exteriorKoszulDGFunctor LinearMap.id _ _ (chartTransitionDifferential_id a i k f s hs))

/-- 概要：遷移環射に沿う dg 底変更を共通環上の i チャート模型へ送る。
方針：規格化した底変更に Koszul の可逆生成元変換を合成する。
規約：KST §3.1。使われ方：任意有限重なりの局所 dg 同値。 -/
def chartTransitionComparisonDGFunctor (a : Fin (r + 1) → R) (i k : Fin (r + 1))
    (f : ChartRing R i →ₐ[R] B) (s : Bˣ) (hs : ↑s = f (chartCoordinate R i k)) :
    EnrichedFunctor (DifferentialGraded.Complex B)
      (DifferentialGraded.ScalarExtension.DGBaseChange (chartTransition i k f s).toRingHom
        (DerivedChartObject a k))
      (ExteriorKoszulObject (chartKoszulDifferential (fun j => algebraMap R B (a j))
        (fun j => f (chartCoordinate R i j)) i)) :=
  EnrichedFunctor.comp (DifferentialGraded.Complex B)
    (chartTransitionNormalizedDGFunctor a i k f s hs)
    (chartExteriorDGFunctor (fun j => algebraMap R B (a j)) (fun j => f (chartCoordinate R i j))
      i k s (by simp) hs)

/-- 概要：共通環での遷移 dg 比較の Hom 写像は可逆。
方針：底変更の cochain 同型と二つの可逆生成元変換を使う。
規約：KST §3.1。使われ方：全有限重なりの局所準同値性。 -/
theorem chartTransitionComparisonDGFunctor_map_isIso (a : Fin (r + 1) → R)
    (i k : Fin (r + 1)) (f : ChartRing R i →ₐ[R] B) (s : Bˣ)
    (hs : ↑s = f (chartCoordinate R i k)) (x y) :
    IsIso ((chartTransitionComparisonDGFunctor a i k f s hs).map x y) := by
  have := chartBaseChangeDGFunctor_map_isIso a k (chartTransition i k f s) x y
  change IsIso (((chartBaseChangeDGFunctor a k (chartTransition i k f s)).map x y ≫
    (exteriorKoszulCochainIso (LinearEquiv.refl B _)
      (chartKoszulDifferential (fun j => algebraMap R B (a j))
        (fun j => chartTransition i k f s (chartCoordinate R k j)) k)
      (chartKoszulDifferential (fun j => algebraMap R B (a j))
        (normalizeCoordinates (fun j => f (chartCoordinate R i j)) s) k)
      (chartTransitionDifferential_id a i k f s hs)).hom) ≫
    (chartExteriorCochainIso (fun j => algebraMap R B (a j))
      (fun j => f (chartCoordinate R i j)) i k s (by simp) hs).hom)
  infer_instance

/-- 概要：共通環での遷移 dg 比較は準同値。
方針：Hom の可逆性と一対象型の本質的全射性を使う。
規約：KST §3.1。使われ方：全有限重なりのチャート模型の比較。 -/
theorem chartTransitionComparisonDGFunctor_quasiEquivalence (a : Fin (r + 1) → R)
    (i k : Fin (r + 1)) (f : ChartRing R i →ₐ[R] B) (s : Bˣ)
    (hs : ↑s = f (chartCoordinate R i k)) :
    DifferentialGraded.QuasiEquivalence (chartTransitionComparisonDGFunctor a i k f s hs) := by
  constructor
  · intro x y
    have := chartTransitionComparisonDGFunctor_map_isIso a i k f s hs x y
    infer_instance
  · apply Functor.essSurj_of_surj
    rintro ⟨y⟩
    change ExteriorKoszulObject (chartKoszulDifferential (fun j => algebraMap R B (a j))
      (fun j => f (chartCoordinate R i j)) i) at y
    cases y
    exact ⟨⟨ExteriorKoszulObject.point⟩, rfl⟩

set_option synthInstance.maxHeartbeats 100000 in
-- 局所化係数環の複体のモノイダル構造の探索に必要。
/-- 概要：任意有限重なりに沿うチャート dg 比較関手。
方針：一般の遷移比較を有限座標積の局所化へ適用する。
規約：KST §3.1。使われ方：全有限 Čech の局所模型。 -/
def finiteOverlapChartDGFunctor (a : Fin (r + 1) → R) (i k : Fin (r + 1))
    (T : Finset (Fin (r + 1))) (hk : k ∈ T) :=
  chartTransitionComparisonDGFunctor a i k (finiteOverlapInclusion R i T)
    (finiteOverlapUnit R i T k hk) (finiteOverlapUnit_val R i T k hk)

set_option synthInstance.maxHeartbeats 100000 in
-- 同じ局所化係数環の豊穣構造の探索に必要。
/-- 概要：任意有限重なりにおけるチャート dg 比較は準同値。
方針：共通環上の一般の準同値定理を使う。
規約：KST §3.1。使われ方：全有限チャート図式の局所比較。 -/
theorem finiteOverlapChartDGFunctor_quasiEquivalence (a : Fin (r + 1) → R)
    (i k : Fin (r + 1)) (T : Finset (Fin (r + 1))) (hk : k ∈ T) :
    DifferentialGraded.QuasiEquivalence (finiteOverlapChartDGFunctor a i k T hk) :=
  chartTransitionComparisonDGFunctor_quasiEquivalence a i k _ _ _

end SerrePositivity.KST.DerivedBlowup
