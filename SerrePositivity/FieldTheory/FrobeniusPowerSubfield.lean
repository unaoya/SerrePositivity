module

public import SerrePositivity.FieldTheory.PBasis
public import Mathlib.RingTheory.AlgebraTower

/-! # p^n 乗部分体と p 単項式基底

概要：標数 `p` の体 `k` の p^n 乗部分体 `k^{p^n}`（`frobeniusPowerSubfield`）と、体の同型 `k ≃ k^{p^n}`。
`b` が `k` の p 基底なら、各成分が `p^n` 未満の指数の単項式 `bᵈ` が `k^{p^n}` 上の `k` の基底になる
（`IsPBasis.frobeniusMonomialBasis`）。有限 p 基底なら `[k : k^{p^n}] = p^{n·|ι|}`。
方針：隣り合う段 `k^{p^n}/k^{p^{n+1}}` の基底は、元の p 基底を Frobenius 冪の同型で移したもの
（`basisOfRingEquiv`）。これを Mathlib の `Basis.smulTower` で積み重ね、商と余りの同値
（`PExponent.radixEquiv`）で添字を `p^n` 未満の指数に付け替える。値は `pMonomial_radixJoin` で読む。
規約：添字集合の有限性も、体が完全であることも仮定しない。
使われ方：p 基底の Frobenius 持ち上げ（`PBasisFrobeniusLift`）、係数の持ち上げ。
-/

@[expose] public section
namespace SerrePositivity

section Subfield

variable (k : Type*) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]

/-- p^n 乗の像の部分体。 -/
def frobeniusPowerSubfield (n : ℕ) : Subfield k := (iterateFrobenius k p n).fieldRange

@[simp] theorem mem_frobeniusPowerSubfield (n : ℕ) (x : k) :
    x ∈ frobeniusPowerSubfield k p n ↔ ∃ y : k, y ^ p ^ n = x := Iff.rfl

/-- Frobenius 冪は体とその像部分体との同型。 -/
noncomputable def frobeniusPowerEquiv (n : ℕ) : k ≃+* frobeniusPowerSubfield k p n :=
  (iterateFrobenius k p n).rangeRestrictFieldEquiv

@[simp] theorem frobeniusPowerEquiv_apply_coe (n : ℕ) (x : k) :
    (frobeniusPowerEquiv k p n x : k) = x ^ p ^ n := rfl

theorem frobeniusPowerSubfield_succ_le (n : ℕ) :
    frobeniusPowerSubfield k p (n + 1) ≤ frobeniusPowerSubfield k p n := by
  intro x hx
  obtain ⟨y, rfl⟩ := (mem_frobeniusPowerSubfield k p (n + 1) x).mp hx
  refine (mem_frobeniusPowerSubfield k p n _).mpr ⟨y ^ p, ?_⟩
  rw [← pow_mul, pow_succ, Nat.mul_comm p (p ^ n)]

end Subfield

section Layer

variable (k : Type*) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]

/-- 隣接する部分体間の係数作用は、包含写像によるもの。 -/
noncomputable instance frobeniusPowerAlgebra (n : ℕ) :
    Algebra (frobeniusPowerSubfield k p (n + 1)) (frobeniusPowerSubfield k p n) :=
  (Subfield.inclusion (frobeniusPowerSubfield_succ_le k p n)).toAlgebra

instance frobeniusPowerIsScalarTower (n : ℕ) :
    IsScalarTower (frobeniusPowerSubfield k p (n + 1)) (frobeniusPowerSubfield k p n) k :=
  IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)

/-- p 乗部分体を、塔の次の段の係数部分体へ移す同型。 -/
noncomputable def frobeniusLayerCoefficientEquiv (n : ℕ) :
    pPowerSubfield k p ≃+* frobeniusPowerSubfield k p (n + 1) :=
  (pPowerEquiv k p).symm.trans (frobeniusPowerEquiv k p (n + 1))

@[simp] theorem frobeniusLayerCoefficientEquiv_apply_coe (n : ℕ)
    (c : pPowerSubfield k p) :
    (frobeniusLayerCoefficientEquiv k p n c : k) = (c : k) ^ p ^ n := by
  change ((pPowerEquiv k p).symm c) ^ p ^ (n + 1) = (c : k) ^ p ^ n
  have hc : ((pPowerEquiv k p).symm c) ^ p = (c : k) :=
    congrArg Subtype.val ((pPowerEquiv k p).apply_symm_apply c)
  rw [pow_succ, Nat.mul_comm (p ^ n) p, pow_mul, hc]

/-- 塔の各段で、係数の同型と元の同型は代数構造の写像と可換。 -/
theorem frobeniusLayer_algebraMap_compat (n : ℕ) (c : pPowerSubfield k p) :
    frobeniusPowerEquiv k p n (algebraMap (pPowerSubfield k p) k c) =
      algebraMap (frobeniusPowerSubfield k p (n + 1)) (frobeniusPowerSubfield k p n)
        (frobeniusLayerCoefficientEquiv k p n c) :=
  Subtype.ext (frobeniusLayerCoefficientEquiv_apply_coe k p n c).symm

variable {k p} {ι : Type*} {b : ι → k}

/-- 塔の一段 `k^{p^n}/k^{p^{n+1}}` の基底。元の p 基底を Frobenius 冪の同型で移したもの。 -/
noncomputable def IsPBasis.frobeniusLayerBasis (hb : IsPBasis k p b) (n : ℕ) :
    Module.Basis (PExponent p ι) (frobeniusPowerSubfield k p (n + 1))
      (frobeniusPowerSubfield k p n) :=
  basisOfRingEquiv hb.basis (frobeniusLayerCoefficientEquiv k p n)
    (frobeniusPowerEquiv k p n) (frobeniusLayer_algebraMap_compat k p n)

@[simp] theorem IsPBasis.frobeniusLayerBasis_apply (hb : IsPBasis k p b) (n : ℕ)
    (d : PExponent p ι) :
    hb.frobeniusLayerBasis n d = frobeniusPowerEquiv k p n (pMonomial b d) := by
  simp [IsPBasis.frobeniusLayerBasis, hb.basis_apply]

end Layer

section MonomialBasis

variable {k : Type*} [Field k] {p : ℕ} [Fact p.Prime] [CharP k p] {ι : Type*} {b : ι → k}

variable (k p ι) in
/-- 0 段目の基底：`k^{p^0} = k` 上の `k` の基底 `{1}`。 -/
noncomputable def frobeniusZeroBasis :
    Module.Basis (PExponent (p ^ 0) ι) (frobeniusPowerSubfield k p 0) k :=
  ((Module.Basis.singleton Unit k).mapCoeffs (frobeniusPowerEquiv k p 0) fun c x ↦ by
      simp only [Algebra.smul_def]
      change c ^ p ^ 0 * x = c * x
      simp).reindex
    ((Equiv.ofUnique Unit (PExponent 1 ι)).trans (PExponent.boundEquiv (pow_zero p).symm))

/-- 各成分が `p^n` 未満の指数の単項式による、`k^{p^n}` 上の `k` の基底。 -/
noncomputable def IsPBasis.frobeniusMonomialBasis (hb : IsPBasis k p b) :
    (n : ℕ) → Module.Basis (PExponent (p ^ n) ι) (frobeniusPowerSubfield k p n) k
  | 0 => frobeniusZeroBasis k p ι
  | n + 1 => ((hb.frobeniusLayerBasis n).smulTower (hb.frobeniusMonomialBasis n)).reindex
      ((PExponent.radixEquiv p (p ^ n)).symm.trans (PExponent.boundEquiv (pow_succ' p n).symm))

@[simp] theorem IsPBasis.frobeniusMonomialBasis_apply (hb : IsPBasis k p b) (n : ℕ)
    (d : PExponent (p ^ n) ι) : hb.frobeniusMonomialBasis n d = pMonomial b d := by
  induction n with
  | zero =>
    have hd : d.val = 0 := Finsupp.ext fun i ↦ by
      have := d.property i
      simp only [pow_zero, Nat.lt_one_iff] at this
      exact this
    rw [IsPBasis.frobeniusMonomialBasis, frobeniusZeroBasis, Module.Basis.reindex_apply,
      Module.Basis.mapCoeffs_apply, Module.Basis.singleton_apply]
    simp [pMonomial, hd]
  | succ n ih =>
    obtain ⟨e, rfl⟩ := ((PExponent.radixEquiv p (p ^ n)).symm.trans
      (PExponent.boundEquiv (pow_succ' p n).symm)).surjective d
    rw [IsPBasis.frobeniusMonomialBasis, Module.Basis.reindex_apply, Equiv.symm_apply_apply,
      Module.Basis.smulTower_apply, hb.frobeniusLayerBasis_apply, ih, Algebra.smul_def]
    change _ = pMonomial b (PExponent.radixJoin p (p ^ n) e)
    rw [pMonomial_radixJoin]
    rfl

/-- 有限 p 基底なら `[k : k^{p^n}] = p^{n·|ι|}`。 -/
theorem IsPBasis.finrank_frobeniusPowerSubfield [Fintype ι] (hb : IsPBasis k p b) (n : ℕ) :
    Module.finrank (frobeniusPowerSubfield k p n) k = p ^ (n * Fintype.card ι) := by
  rw [Module.finrank_eq_card_basis (hb.frobeniusMonomialBasis n), PExponent.card, ← pow_mul]

end MonomialBasis

end SerrePositivity
