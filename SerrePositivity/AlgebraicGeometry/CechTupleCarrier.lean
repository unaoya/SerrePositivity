module

public import SerrePositivity.AlgebraicGeometry.CechTupleReindex
public import SerrePositivity.AlgebraicGeometry.ProjectiveCechComplex

/-!
概要：整数鎖の台の包含を、細分で動く頂点集合に対して管理する。
方針：指定した頂点集合のタプルで生成される部分加群の普遍性を用いる。
規約：始域と終域の頂点集合は異なってよい。
使われ方：二通りの細分のホモトピーを、切断の制限付き評価へ移す。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open scoped BigOperators
variable {ι κ : Type*}

/-- 生成元の台の条件から、鎖の写像の台の条件を得る。 -/
theorem cechTupleChainsOn_map {T : Set ι} {S : Set κ} {k l : ℕ}
    (F : CechTupleChains ι k →ₗ[ℤ] CechTupleChains κ l)
    (hF : ∀ t, (∀ i, t i ∈ T) → F (Finsupp.single t 1) ∈ cechTupleChainsOn S l)
    {x : CechTupleChains ι k} (hx : x ∈ cechTupleChainsOn T k) :
    F x ∈ cechTupleChainsOn S l := by
  have hle : cechTupleChainsOn T k ≤ (cechTupleChainsOn S l).comap F := by
    change Finsupp.supported ℤ ℤ {t : Fin k → ι | ∀ i, t i ∈ T} ≤ _
    rw [Finsupp.supported_eq_span_single, Submodule.span_le]
    rintro _ ⟨t, ht, rfl⟩
    exact hF t ht
  exact hle hx

/-- 台を指定した生成元の所属。 -/
theorem cechTupleChainsOn_single_mem {T : Set ι} {k : ℕ} {t : Fin k → ι}
    (ht : ∀ i, t i ∈ T) : Finsupp.single t (1 : ℤ) ∈ cechTupleChainsOn T k :=
  Finsupp.single_mem_supported ℤ 1 ht

/-- 境界は指定した頂点集合を保つ。 -/
theorem cechTupleChainsOn_boundary {T : Set ι} {k : ℕ}
    {x : CechTupleChains ι (k + 1)} (hx : x ∈ cechTupleChainsOn T (k + 1)) :
    cechTupleBoundary k x ∈ cechTupleChainsOn T k := by
  apply cechTupleChainsOn_map (cechTupleBoundary k) _ hx
  intro t ht
  simp only [cechTupleBoundary, Finsupp.linearCombination_single, one_smul]
  exact Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _
    (cechTupleChainsOn_single_mem fun j ↦ ht (i.succAbove j))

/-- 集合内の頂点の先頭追加は、その集合を保つ。 -/
theorem cechTupleChainsOn_prepend {T : Set ι} {k : ℕ} {v : ι} (hv : v ∈ T)
    {x : CechTupleChains ι k} (hx : x ∈ cechTupleChainsOn T k) :
    cechTuplePrepend v k x ∈ cechTupleChainsOn T (k + 1) := by
  apply cechTupleChainsOn_map (cechTuplePrepend v k) _ hx
  intro t ht
  simp only [cechTuplePrepend, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
  exact cechTupleChainsOn_single_mem
    (Fin.cases (by simpa using hv) (fun i ↦ by simpa using ht i))

/-- 再添字付けは、頂点集合の像へ鎖を送る。 -/
theorem cechTupleChainsOn_reindex (ρ : ι → κ) {T : Set ι} {S : Set κ} {k : ℕ}
    (hρ : ∀ i ∈ T, ρ i ∈ S) {x : CechTupleChains ι k}
    (hx : x ∈ cechTupleChainsOn T k) :
    cechTupleReindex ρ k x ∈ cechTupleChainsOn S k := by
  apply cechTupleChainsOn_map (cechTupleReindex ρ k) _ hx
  intro t ht
  rw [cechTupleReindex_single]
  exact cechTupleChainsOn_single_mem fun i ↦ hρ _ (ht i)

/-- 鎖写像で保たれる一つの頂点集合は、比較ホモトピーでも保たれる。 -/
theorem cechTupleComparisonHomotopy_stable_carrier
    (P : ∀ k, CechTupleChains ι k →ₗ[ℤ] CechTupleChains ι k) (T : Set ι)
    (hP : ∀ k (x : CechTupleChains ι k),
      x ∈ cechTupleChainsOn T k → P k x ∈ cechTupleChainsOn T k)
    (k : ℕ) (x : CechTupleChains ι k) (hx : x ∈ cechTupleChainsOn T k) :
    cechTupleComparisonHomotopy P k x ∈ cechTupleChainsOn T (k + 1) := by
  induction k with
  | zero => exact (cechTupleChainsOn T 1).zero_mem
  | succ k ih =>
    apply cechTupleChainsOn_map (cechTupleComparisonHomotopy P (k + 1)) _ hx
    intro t ht
    rw [cechTupleComparisonHomotopy_succ_single]
    have hs := cechTupleChainsOn_single_mem ht
    exact cechTupleChainsOn_prepend (ht 0) <|
      (cechTupleChainsOn T (k + 1)).sub_mem
        ((cechTupleChainsOn T (k + 1)).sub_mem hs (hP _ _ hs))
        (ih _ (cechTupleChainsOn_boundary hs))

end SerrePositivity.AlgebraicGeometry
