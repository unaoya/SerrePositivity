module

public import SerrePositivity.PerfectComplex.NormalizedEuler
public import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated

/-! # 合成写像の錐の Euler 加法性

合成の八面体を実際の写像錐のホモトピー同値として使う。
三つの錐のホモロジーについてだけ長さの有限性と冪ねじれ性を要求し、
元の複体についてはこれらを要求しない。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits

variable {R : Type u} [CommRing R] {J : Ideal R} (lam : NormalizedLength R J)

/-- 合成写像の錐の Euler 評価は、二つの写像の錐の Euler 評価の和。
有界性は最初の錐と合成の錐にだけ要求すれば十分である。 -/
theorem lambdaEuler_mappingCone_comp
    {P Q W : CochainComplex (ModuleCat.{u} R) ℤ} (f : P ⟶ Q) (g : Q ⟶ W)
    (hf : ∃ a b : ℤ, ∀ q, q < a ∨ b < q → IsZero ((Cone.cone f).X q))
    (hfg : ∃ a b : ℤ, ∀ q, q < a ∨ b < q → IsZero ((Cone.cone (f ≫ g)).X q))
    (tf : ∀ q, IsPowTorsion J ((Cone.cone f).homology q))
    (tfg : ∀ q, IsPowTorsion J ((Cone.cone (f ≫ g)).homology q))
    (tg : ∀ q, IsPowTorsion J ((Cone.cone g).homology q))
    (lf : ∀ q, lam.len ((Cone.cone f).homology q) ≠ ⊤)
    (lfg : ∀ q, lam.len ((Cone.cone (f ≫ g)).homology q) ≠ ⊤)
    (lg : ∀ q, lam.len ((Cone.cone g).homology q) ≠ ⊤) :
    lambdaEuler lam (Cone.cone (f ≫ g)) =
      lambdaEuler lam (Cone.cone f) + lambdaEuler lam (Cone.cone g) := by
  let a := (CochainComplex.mappingConeCompTriangle f g).mor₁
  let e := CochainComplex.mappingConeCompHomotopyEquiv f g
  have hb : ∃ b₁ b₂ : ℤ, ∀ q, q < b₁ ∨ b₂ < q → IsZero ((Cone.cone a).X q) := by
    obtain ⟨a₁, b₁, h₁⟩ := hf
    obtain ⟨a₂, b₂, h₂⟩ := hfg
    refine ⟨min a₁ a₂ - 1, max b₁ b₂, fun q hq ↦ ?_⟩
    rw [CochainComplex.mappingCone.isZero_X_iff]
    constructor
    · apply h₁
      rcases hq with hq | hq
      · left; omega
      · right; omega
    · apply h₂
      rcases hq with hq | hq
      · left; omega
      · right; omega
  have tc : ∀ q, IsPowTorsion J ((Cone.cone a).homology q) := fun q ↦
    IsPowTorsion.of_equiv (e.toHomologyIso q).toLinearEquiv (tg q)
  have lc : ∀ q, lam.len ((Cone.cone a).homology q) ≠ ⊤ := by
    intro q
    rw [← lam.len_congr _ _ (e.toHomologyIso q).toLinearEquiv]
    exact lg q
  have h := lambdaEuler_cone lam a hfg hb tf tfg tc lf lfg lc
  have he := lambdaEuler_eq_of_homotopyEquiv lam e
  change lambdaEuler lam (Cone.cone g) = lambdaEuler lam (Cone.cone a) at he
  rw [← he] at h
  change lambdaEuler lam (Cone.cone g) =
    lambdaEuler lam (Cone.cone (f ≫ g)) - lambdaEuler lam (Cone.cone f) at h
  linarith

/-- スカラー乗法の正冪の錐の Euler 評価は指数倍。
条件は各正冪の錐にのみ課し、元の複体には長さ・冪ねじれの条件を課さない。 -/
theorem lambdaEuler_scalarCone_pow (P : CochainComplex (ModuleCat.{u} R) ℤ) (a : R)
    (hb : ∀ n : ℕ, 0 < n → ∃ b₁ b₂ : ℤ, ∀ q,
      q < b₁ ∨ b₂ < q → IsZero ((Cone.cone (smulId (a ^ n) P)).X q))
    (ht : ∀ n : ℕ, 0 < n → ∀ q,
      IsPowTorsion J ((Cone.cone (smulId (a ^ n) P)).homology q))
    (hl : ∀ n : ℕ, 0 < n → ∀ q,
      lam.len ((Cone.cone (smulId (a ^ n) P)).homology q) ≠ ⊤)
    (k : ℕ) (hk : 0 < k) :
    lambdaEuler lam (Cone.cone (smulId (a ^ k) P)) =
      (k : ℝ) * lambdaEuler lam (Cone.cone (smulId a P)) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  induction n with
  | zero => simp
  | succ n ih =>
      have hc : smulId (a ^ (n + 1)) P ≫ smulId a P = smulId (a ^ (n + 2)) P := by
        simp [smulId, ← mul_smul, pow_succ, mul_comm]
      have ht₁ := ht (n + 1) (by omega)
      have hl₁ := hl (n + 1) (by omega)
      have ht₂ := ht (n + 2) (by omega)
      have hl₂ := hl (n + 2) (by omega)
      have hb₂ := hb (n + 2) (by omega)
      have ht₃ := ht 1 one_pos
      have hl₃ := hl 1 one_pos
      rw [pow_one] at ht₃ hl₃
      rw [← hc] at ht₂ hl₂ hb₂
      have he := lambdaEuler_mappingCone_comp lam (smulId (a ^ (n + 1)) P)
        (smulId a P) (hb (n + 1) (by omega)) hb₂ ht₁ ht₂ ht₃ hl₁ hl₂ hl₃
      rw [hc] at he
      rw [he, ih (by omega)]
      push_cast
      ring

end SerrePositivity
