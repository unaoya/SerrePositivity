module

public import SerrePositivity.AlgebraicGeometry.CechTupleReindex

/-!
概要：二通りの頂点の写像が誘導する整数鎖の写像を比較する。
方針：添字の直和に既存の縮約を適用し、両側から再添字付けする。
規約：増大鎖の全次数を扱う。被覆に関する仮定は用いない。
使われ方：細分の添字の選択から Čech H 上の射が独立であること。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
variable {ι κ : Type*}

/-- 直和添字の左側を一つ目の写像で右側へ移す。 -/
def cechRefinementAmbient (ρ : κ → ι) : κ ⊕ ι → κ ⊕ ι :=
  Sum.elim (Sum.inr ∘ ρ) Sum.inr

/-- 直和添字を二つ目の写像により元の目標へ戻す。 -/
def cechRefinementProjection (σ : κ → ι) : κ ⊕ ι → ι := Sum.elim σ id

/-- 二つの再添字付けをつなぐ整数鎖のホモトピー。 -/
def cechTupleRefinementHomotopy (ρ σ : κ → ι) (k : ℕ) :
    CechTupleChains κ k →ₗ[ℤ] CechTupleChains ι (k + 1) :=
  (cechTupleReindex (cechRefinementProjection σ) (k + 1)).comp
    ((cechTupleComparisonHomotopy (cechTupleReindex (cechRefinementAmbient ρ)) k).comp
      (cechTupleReindex Sum.inl k))

/-- 再添字付けの比較ホモトピーの方程式。 -/
theorem cechTupleRefinementHomotopy_identity (ρ σ : κ → ι) (k : ℕ) :
    (cechTupleBoundary (k + 1)).comp (cechTupleRefinementHomotopy ρ σ (k + 1)) +
      (cechTupleRefinementHomotopy ρ σ k).comp (cechTupleBoundary k) =
        cechTupleReindex σ (k + 1) - cechTupleReindex ρ (k + 1) := by
  let P := cechTupleReindex (cechRefinementAmbient ρ)
  let Q := cechTupleReindex (cechRefinementProjection σ)
  let I := cechTupleReindex (Sum.inl : κ → κ ⊕ ι)
  have hp (i : ℕ) (x : CechTupleChains (κ ⊕ ι) (i + 1)) :
      cechTupleBoundary i (P (i + 1) x) = P i (cechTupleBoundary i x) :=
    LinearMap.congr_fun (cechTupleReindex_boundary (cechRefinementAmbient ρ) i) x
  have hi (i : ℕ) (x : CechTupleChains κ (i + 1)) :
      cechTupleBoundary i (I (i + 1) x) = I i (cechTupleBoundary i x) :=
    LinearMap.congr_fun (cechTupleReindex_boundary Sum.inl i) x
  have hq (i : ℕ) (x : CechTupleChains (κ ⊕ ι) (i + 1)) :
      cechTupleBoundary i (Q (i + 1) x) = Q i (cechTupleBoundary i x) :=
    LinearMap.congr_fun (cechTupleReindex_boundary (cechRefinementProjection σ) i) x
  have hQI : (Q (k + 1)).comp (I (k + 1)) = cechTupleReindex σ (k + 1) := by
    rw [cechTupleReindex_comp]
    rfl
  have hQPI : (Q (k + 1)).comp ((P (k + 1)).comp (I (k + 1))) =
      cechTupleReindex ρ (k + 1) := by
    rw [cechTupleReindex_comp, cechTupleReindex_comp]
    rfl
  apply LinearMap.ext
  intro x
  change cechTupleBoundary (k + 1)
      (Q (k + 2) (cechTupleComparisonHomotopy P (k + 1) (I (k + 1) x))) +
    Q (k + 1) (cechTupleComparisonHomotopy P k (I k (cechTupleBoundary k x))) = _
  rw [hq, ← hi]
  rw [← map_add]
  have hh := LinearMap.congr_fun (cechTupleComparisonHomotopy_identity P
    (cechTupleReindex_zero (cechRefinementAmbient ρ)) hp k) (I (k + 1) x)
  change Q (k + 1)
    ((cechTupleBoundary (k + 1) (cechTupleComparisonHomotopy P (k + 1) (I (k + 1) x))) +
      cechTupleComparisonHomotopy P k (cechTupleBoundary k (I (k + 1) x))) = _
  rw [show cechTupleBoundary (k + 1)
      (cechTupleComparisonHomotopy P (k + 1) (I (k + 1) x)) +
        cechTupleComparisonHomotopy P k (cechTupleBoundary k (I (k + 1) x)) =
      I (k + 1) x - P (k + 1) (I (k + 1) x) from hh]
  rw [map_sub]
  exact congrArg₂ (· - ·) (LinearMap.congr_fun hQI x) (LinearMap.congr_fun hQPI x)

end SerrePositivity.AlgebraicGeometry
