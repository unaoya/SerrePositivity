module

public import SerrePositivity.AlgebraicGeometry.CechTupleRefinementHomotopy
public import SerrePositivity.AlgebraicGeometry.CechTupleCarrier

/-!
概要：細分の選択の比較ホモトピーに現れる頂点を制御する。
方針：二つの像の和集合を、直和添字上の安定な集合から得る。
規約：ホモトピーの値の台は入力の二つの像の中にある。
使われ方：開集合の包含による係数の制限を、比較ホモトピーに適用する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
variable {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]

/-- ホモトピーの値の頂点は、入力タプルの二つの像に含まれる。 -/
theorem cechTupleRefinementHomotopy_carrier (ρ σ : κ → ι) {k : ℕ} (t : Fin k → κ) :
    cechTupleRefinementHomotopy ρ σ k (Finsupp.single t 1) ∈
      cechTupleChainsOn (↑((cechTupleSupport t).image ρ ∪ (cechTupleSupport t).image σ))
        (k + 1) := by
  let T : Set (κ ⊕ ι) := {z | z.elim
    (fun j ↦ j ∈ cechTupleSupport t) (fun i ↦ i ∈ (cechTupleSupport t).image ρ)}
  have hP (n : ℕ) (x : CechTupleChains (κ ⊕ ι) n) (hx : x ∈ cechTupleChainsOn T n) :
      cechTupleReindex (cechRefinementAmbient ρ) n x ∈ cechTupleChainsOn T n := by
    apply cechTupleChainsOn_reindex _ _ hx
    intro z hz
    cases z with
    | inl j =>
      change j ∈ cechTupleSupport t at hz
      exact Finset.mem_image.mpr ⟨j, hz, rfl⟩
    | inr i =>
      change i ∈ (cechTupleSupport t).image ρ at hz
      exact hz
  have hI : cechTupleReindex (Sum.inl : κ → κ ⊕ ι) k (Finsupp.single t 1) ∈
      cechTupleChainsOn T k := by
    rw [cechTupleReindex_single]
    exact cechTupleChainsOn_single_mem fun i ↦
      Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  have hH := cechTupleComparisonHomotopy_stable_carrier
    (cechTupleReindex (cechRefinementAmbient ρ)) T hP k _ hI
  apply cechTupleChainsOn_reindex (cechRefinementProjection σ) _ hH
  intro z hz
  cases z with
  | inl j =>
    change j ∈ cechTupleSupport t at hz
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j, hz, rfl⟩)
  | inr i =>
    change i ∈ (cechTupleSupport t).image ρ at hz
    exact Finset.mem_union_left _ hz

/-- ホモトピーの各出力タプルの台は、二つの像の和集合の中にある。 -/
theorem cechTupleRefinementHomotopy_support (ρ σ : κ → ι) {k : ℕ} (t : Fin k → κ)
    (s : Fin (k + 1) → ι)
    (hs : s ∈ (cechTupleRefinementHomotopy ρ σ k (Finsupp.single t 1)).support) :
    cechTupleSupport s ⊆ (cechTupleSupport t).image ρ ∪ (cechTupleSupport t).image σ := by
  have h := cechTupleRefinementHomotopy_carrier ρ σ t
  have hS := (Finsupp.mem_supported ℤ _).mp h
  intro i hi
  obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hi
  exact hS hs a

end SerrePositivity.AlgebraicGeometry
