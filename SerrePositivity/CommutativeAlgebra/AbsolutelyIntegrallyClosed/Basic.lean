module


public meta import SerrePositivity.Util.Citation
public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.Lifts
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.Localization.Integral

/-! # 絶対整閉な環

## 概要

可換環 S が絶対整閉（`IsAbsolutelyIntegrallyClosed`）であるとは、次数が正のモニック多項式がすべて S に根を持つことをいう（BS 著者版 Theorem 7.14 の用語）。任意の元は両立する p 冪根の系を持つ。絶対整閉性は全射像・商・局所化で保たれ、絶対整閉な体は代数閉体で、剰余体も代数閉である。有限エタール代数の剰余体でのファイバーは代数として比較できる。

## 方針

根の存在をモニック多項式に適用するだけで示す。ファイバーの比較は実際の代数同型として与える。

## 規約

原典は「任意のモニック多項式が解を持つ」と書くが、次数 0 のモニック多項式 1 は根を持たないので、次数が正という条件を明示する。零環では条件は自明に成り立つ。`IsAbsolutelyIntegrallyClosed.isAlgClosed` は残す。

## 使われ方

BhattScholze の André の平坦性・almost 数学、CLMST の局所的な比較。
-/

@[expose] public noncomputable section

universe u

section AbsolutelyIntegrallyClosedPart

open Polynomial

namespace SerrePositivity

/-- 環 `S` が絶対整閉であること。次数が正の任意のモニック多項式が `S` に根を持つ。
BS 著者版 Theorem 7.14 の用語で、André の平坦性補題が与える拡大の性質である。 -/
def IsAbsolutelyIntegrallyClosed (S : Type u) [CommRing S] : Prop :=
  ∀ P : S[X], P.Monic → 0 < P.natDegree → ∃ x : S, P.IsRoot x

/-- 絶対整閉な環では、任意の元 `a` が両立する `n` 乗根の系を持つ（BS 著者版 Theorem 7.14 の第二文の根の主張の一般化）。
  すなわち
`r 0 = a` かつ各 `k` で `r (k+1) ^ n = r k` を満たす列 `r` がある。ただし `0 < n`。
各段で `X^n - r k` が次数 `n` のモニック多項式であることから、根を順に選ぶ。 -/
theorem IsAbsolutelyIntegrallyClosed.exists_compatible_pow_roots {S : Type u} [CommRing S]
    (hS : IsAbsolutelyIntegrallyClosed S) {n : ℕ} (hn : 0 < n) (a : S) :
    ∃ r : ℕ → S, r 0 = a ∧ ∀ k, r (k + 1) ^ n = r k := by
  have hroot : ∀ b : S, ∃ x : S, x ^ n = b := by
    intro b
    by_cases h1 : (1 : S) = 0
    · exact ⟨0, Subsingleton.elim (h := subsingleton_of_zero_eq_one h1.symm) _ _⟩
    have : Nontrivial S := ⟨⟨1, 0, h1⟩⟩
    obtain ⟨x, hx⟩ := hS (X ^ n - C b) (monic_X_pow_sub_C b hn.ne')
      (by rw [natDegree_X_pow_sub_C]; exact hn)
    exact ⟨x, by simpa [sub_eq_zero] using hx⟩
  choose root hroot using hroot
  refine ⟨fun k ↦ Nat.rec a (fun _ b ↦ root b) k, rfl, fun k ↦ hroot _⟩

end SerrePositivity

end AbsolutelyIntegrallyClosedPart

section AbsolutelyIntegrallyClosedFibersPart

namespace SerrePositivity
open Polynomial
open scoped TensorProduct

/-- Absolute integral closedness descends through every surjective ring map. -/
theorem IsAbsolutelyIntegrallyClosed.of_surjective
    {R S : Type u} [CommRing R] [CommRing S] (hR : IsAbsolutelyIntegrallyClosed R)
    (f : R →+* S) (hf : Function.Surjective f) : IsAbsolutelyIntegrallyClosed S := by
  intro P hP hdeg
  obtain ⟨Q, hQ, hdegree, hmonic⟩ := Polynomial.lifts_and_natDegree_eq_and_monic
    (Polynomial.mem_lifts_of_surjective hf P) hP
  obtain ⟨x, hx⟩ := hR Q hmonic (hdegree ▸ hdeg)
  refine ⟨f x, ?_⟩
  change P.eval (f x) = 0
  rw [← hQ, Polynomial.eval_map]
  rw [Polynomial.eval₂_at_apply]
  rw [hx, map_zero]

theorem IsAbsolutelyIntegrallyClosed.quotient
    {R : Type u} [CommRing R] (hR : IsAbsolutelyIntegrallyClosed R) (I : Ideal R) :
    IsAbsolutelyIntegrallyClosed (R ⧸ I) :=
  hR.of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective

/-- Absolute integral closedness persists under arbitrary localization, including
localization at a zero divisor. Monic lifting is applied after clearing denominators. -/
theorem IsAbsolutelyIntegrallyClosed.localization
    {R : Type u} [CommRing R] (hR : IsAbsolutelyIntegrallyClosed R)
    (M : Submonoid R) (S : Type u) [CommRing S] [Algebra R S] [IsLocalization M S] :
    IsAbsolutelyIntegrallyClosed S := by
  intro P hP hdeg
  let s := IsLocalization.commonDenom M P.support P.coeff
  have hl : P.scaleRoots (algebraMap R S s) ∈ Polynomial.lifts (algebraMap R S) := by
    apply IsLocalization.scaleRoots_commonDenom_mem_lifts M P
    rw [hP.leadingCoeff]
    exact one_mem _
  obtain ⟨Q, hQ, hdegree, hmonic⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hl
    ((Polynomial.monic_scaleRoots_iff _).mpr hP)
  obtain ⟨x, hx⟩ := hR Q hmonic (by simpa only [hdegree, Polynomial.natDegree_scaleRoots] using hdeg)
  have hscaled : (P.scaleRoots (algebraMap R S s)).eval (algebraMap R S x) = 0 := by
    rw [← hQ, Polynomial.eval_map_apply, hx, map_zero]
  obtain ⟨u, hu⟩ := IsLocalization.map_units S s
  let y : S := ↑u⁻¹ * algebraMap R S x
  have hmul : algebraMap R S s * y = algebraMap R S x := by
    rw [← hu]
    simp [y]
  have he := P.scaleRoots_eval_mul y (algebraMap R S s)
  rw [hmul, hscaled] at he
  refine ⟨y, ?_⟩
  exact ((IsLocalization.map_units S s).pow P.natDegree).mul_right_eq_zero.mp he.symm

/-- On a field the monic-root condition implies the standard algebraic closedness class. -/
theorem IsAbsolutelyIntegrallyClosed.isAlgClosed
    {K : Type u} [Field K] (hK : IsAbsolutelyIntegrallyClosed K) : IsAlgClosed K := by
  apply IsAlgClosed.of_exists_root
  intro P hP hirr
  exact hK P hP hirr.natDegree_pos

/-- Every maximal residue field of the original ring is algebraically closed. -/
theorem IsAbsolutelyIntegrallyClosed.residue_isAlgClosed
    {R : Type u} [CommRing R] (hR : IsAbsolutelyIntegrallyClosed R)
    (m : Ideal R) [m.IsMaximal] :
    letI := Ideal.Quotient.field m
    IsAlgClosed (R ⧸ m) := by
  letI := Ideal.Quotient.field m
  exact (hR.quotient m).isAlgClosed

/-- A finite étale fiber over a maximal residue field splits into a finite product
of that same residue field, including the rank-zero algebra. -/
theorem IsAbsolutelyIntegrallyClosed.finiteEtale_residueFiber_exists_algEquiv
    {R : Type u} [CommRing R] (hR : IsAbsolutelyIntegrallyClosed R)
    (m : Ideal R) [m.IsMaximal]
    (A : Type u) [CommRing A] [Algebra R A] [Module.Finite R A] [Algebra.Etale R A] :
    letI := Ideal.Quotient.field m
    ∃ r : ℕ, Nonempty ((R ⧸ m) ⊗[R] A ≃ₐ[R ⧸ m] (Fin r → R ⧸ m)) := by
  letI := Ideal.Quotient.field m
  letI := hR.residue_isAlgClosed m
  let K := R ⧸ m
  let B := K ⊗[R] A
  let e := Algebra.FormallyEtale.equivPiOfIsSepClosed K B
  letI : IsArtinianRing B := isArtinian_of_tower K inferInstance
  letI := Fintype.ofFinite (PrimeSpectrum B)
  exact ⟨Fintype.card (PrimeSpectrum B),
    ⟨e.trans (AlgEquiv.piCongrLeft' K (fun _ : PrimeSpectrum B => K)
      (Fintype.equivFin (PrimeSpectrum B)))⟩⟩

end SerrePositivity

end AbsolutelyIntegrallyClosedFibersPart

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite BS19 "Thm 7.14"] _root_.SerrePositivity.IsAbsolutelyIntegrallyClosed.exists_compatible_pow_roots
