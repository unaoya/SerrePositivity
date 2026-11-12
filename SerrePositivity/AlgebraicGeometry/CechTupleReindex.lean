module

public import SerrePositivity.AlgebraicGeometry.CechTupleContraction

/-!
概要：頂点の写像による全タプルの増大整数鎖の写像。
方針：タプルの合成による自由加群の写像を使う。
規約：重複した頂点も許し、増大項も含む。
使われ方：二通りの細分の選択を比較する鎖ホモトピー。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open scoped BigOperators
variable {ι κ τ : Type*}

/-- 頂点の写像に沿う、タプルの整数鎖の再添字付け。 -/
def cechTupleReindex (ρ : ι → κ) (k : ℕ) :
    CechTupleChains ι k →ₗ[ℤ] CechTupleChains κ k :=
  Finsupp.lmapDomain ℤ ℤ (fun t ↦ ρ ∘ t)

/-- 再添字付けはタプルの生成元をそのまま写す。 -/
theorem cechTupleReindex_single (ρ : ι → κ) (k : ℕ) (t : Fin k → ι) (a : ℤ) :
    cechTupleReindex ρ k (Finsupp.single t a) = Finsupp.single (ρ ∘ t) a := by
  simp only [cechTupleReindex, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

/-- 再添字付けは合成を保つ。 -/
theorem cechTupleReindex_comp (ρ : ι → κ) (σ : κ → τ) (k : ℕ) :
    (cechTupleReindex σ k).comp (cechTupleReindex ρ k) = cechTupleReindex (σ ∘ ρ) k :=
  (Finsupp.lmapDomain_comp ℤ ℤ _ _).symm

/-- 長さ零の再添字付けは、添字の自己写像では恒等。 -/
theorem cechTupleReindex_zero (ρ : ι → ι) : cechTupleReindex ρ 0 = LinearMap.id := by
  apply Finsupp.lhom_ext
  intro t a
  rw [cechTupleReindex_single]
  congr 1
  exact Subsingleton.elim _ _

/-- 頂点の再添字付けは増大境界と可換。 -/
theorem cechTupleReindex_boundary (ρ : ι → κ) (k : ℕ) :
    (cechTupleBoundary k).comp (cechTupleReindex ρ (k + 1)) =
      (cechTupleReindex ρ k).comp (cechTupleBoundary k) := by
  apply Finsupp.lhom_ext
  intro t a
  rw [← Finsupp.smul_single_one t a, map_smul, map_smul]
  congr 1
  simp only [LinearMap.comp_apply, cechTupleReindex_single, cechTupleBoundary,
    Finsupp.linearCombination_single, one_smul, map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro i _
  rfl

end SerrePositivity.AlgebraicGeometry
