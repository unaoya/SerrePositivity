module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.WittAdicCompleteness
public import SerrePositivity.BhattScholze.Prism.Basic.OrientedPrism
public import SerrePositivity.BhattScholze.Delta.Free.RelativeFreeWitt
import all SerrePositivity.BhattScholze.Delta.Distinguished.PrimeLocalIntegers

/-!
# Witt 環の結晶 prism と係数射

## 概要
p 正則な p 進完備環の Witt 環を結晶 prism にし、剰余環がその条件を満たす
向き付き prism から Witt 結晶 prism への係数射を作る。

## 方針
Frobenius が mod p で p 乗に一致することを、自由 δ 変数の Witt 座標で確認する。
係数射には Witt lift の後の Frobenius を使う。

## 規約
Witt 結晶 prism の生成元は p。第 0 成分との合成は元の Frobenius を剰余に送る。

## 使われ方
BS 著者版 Theorem 6.4 の `ψ` と、結晶比較の底変換。
-/

public noncomputable section

universe u

namespace SerrePositivity.BhattScholze.Prismatic

open WittVector

variable (p : ℕ) [Fact p.Prime]

/-- Witt Frobenius は Witt 環の p による商上で p 乗となる。 -/
theorem wittFrobenius_sub_pow_dvd {C : Type u} [CommRing C] (x : WittVector p C) :
    (p : WittVector p C) ∣ WittVector.frobenius x - x ^ p := by
  let σ := ULift.{u} Unit
  let F := RelativeFreeDeltaRing (R := ℤ) σ
  let D := relativeFreeDeltaStructure σ (integerDelta p)
  let s : σ := ⟨()⟩
  let z : F := MvPolynomial.X (s, 0)
  have hpℤ : Function.Injective (fun x : ℤ => (p : ℤ) * x) := by
    have h : (p : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
    exact fun _ _ hxy => mul_left_cancel₀ h hxy
  have hpF : Function.Injective (fun x : F => (p : F) * x) := by
    simpa only [IsSMulRegular, map_natCast, smul_eq_mul] using
      (show IsSMulRegular ℤ (p : ℤ) from hpℤ).of_flat (S := F)
  let e := relativeFreeWittCoordinateEquiv (σ := σ) (integerDelta p) hpℤ
  let ev : F →+* C := MvPolynomial.eval₂Hom (Int.castRingHom C) (fun j => x.coeff j.2)
  let q := ev.comp e.symm.toRingEquiv.toRingHom
  have hq : WittVector.map q (deltaWittGhostVector D z) = x := by
    ext n
    change ev (e.symm (relativeFreeWittGhostCoefficient (integerDelta p) s n)) = x.coeff n
    rw [relativeFreeWittCoordinateEquiv_symm_coefficient]
    exact MvPolynomial.eval₂_X _ _ _
  let y := WittVector.map q (deltaWittGhostVector D (D.delta z))
  refine ⟨y, ?_⟩
  have h := deltaWittGhostVector_frobenius_formula_map D
    (witt_ghostMap_injective_of_mul_prime_injective p F hpF) q z
  rw [(WittVector.frobenius_isPoly p).map, hq] at h
  exact sub_eq_iff_eq_add.mpr (by simpa only [y, add_comm] using h)

variable {p} {C : Type u} [CommRing C]
variable (hpC : Function.Injective (fun x : C => (p : C) * x))

/-- p 正則な係数環上の Witt 環の δ 構造。 -/
def wittCrystallineDelta : DeltaStructure p (WittVector p C) :=
  (DeltaStructure.existsUnique_of_frobeniusLift (witt_mul_prime_injective p C hpC)
    WittVector.frobenius (wittFrobenius_sub_pow_dvd p)).exists.choose

theorem wittCrystallineDelta_frobenius :
    (wittCrystallineDelta hpC).frobeniusLift = WittVector.frobenius :=
  (DeltaStructure.existsUnique_of_frobeniusLift (witt_mul_prime_injective p C hpC)
    WittVector.frobenius (wittFrobenius_sub_pow_dvd p)).exists.choose_spec

/-- p 正則な p 進完備環上の Witt 結晶 prism。 -/
@[expose] def wittCrystallinePrism [IsAdicComplete (Ideal.span {(p : C)}) C] :
    OrientedPrism p (WittVector p C) := by
  letI := witt_isAdicComplete p C hpC
  exact OrientedPrism.crystalline (wittCrystallineDelta hpC) (witt_mul_prime_injective p C hpC)

variable {A : Type u} [CommRing A] (P : OrientedPrism p A)
variable (hpA : Function.Injective (fun x : A => (p : A) * x))

local notation "R" => (A ⧸ P.ideal)
local notation "q" => Ideal.Quotient.mk P.ideal
local notation "w" => deltaWittGhostRingHom P.deltaStructure
  (witt_ghostMap_injective_of_mul_prime_injective p A hpA)

/-- 向き付き prism から剰余環の Witt 環への係数射。 -/
def psiRing : A →+* WittVector p R :=
  WittVector.frobenius.comp ((WittVector.map q).comp w)

/-- 係数射の第 0 成分は剰余に送った元の Frobenius。 -/
theorem wZero_psi : (wZero p R).comp (psiRing P hpA) = (q).comp P.deltaStructure.frobeniusLift := by
  apply RingHom.ext
  intro a
  change (WittVector.frobenius (WittVector.map q (w a))).coeff 0 = _
  rw [← (WittVector.frobenius_isPoly p).map]
  have h : WittVector.frobenius (w a) = w (P.deltaStructure.frobeniusLift a) :=
    deltaWittGhostVector_frobenius P.deltaStructure
      (witt_ghostMap_injective_of_mul_prime_injective p A hpA) a
  rw [h]
  rfl

/-- 係数射は結晶 prism への射になる。 -/
def psiPrism (hpR : Function.Injective (fun x : R => (p : R) * x))
    [IsAdicComplete (Ideal.span {(p : R)}) R] :
    OrientedPrism.Hom P (wittCrystallinePrism hpR) where
  toRingHom := psiRing P hpA
  map_delta := by
    apply DeltaStructure.isDeltaHom_of_map_frobeniusLift _ (witt_mul_prime_injective p R hpR)
    intro a
    change psiRing P hpA (P.deltaStructure.frobeniusLift a) =
      (wittCrystallineDelta hpR).frobeniusLift (psiRing P hpA a)
    rw [wittCrystallineDelta_frobenius]
    change WittVector.frobenius (WittVector.map q (w (P.deltaStructure.frobeniusLift a))) =
      WittVector.frobenius (WittVector.frobenius (WittVector.map q (w a)))
    have h : WittVector.frobenius (w a) = w (P.deltaStructure.frobeniusLift a) :=
      deltaWittGhostVector_frobenius P.deltaStructure
        (witt_ghostMap_injective_of_mul_prime_injective p A hpA) a
    rw [← h, (WittVector.frobenius_isPoly p).map]
  ideal_le := by
    change Ideal.span {P.generator} ≤ Ideal.comap (psiRing P hpA) (wittCrystallinePrism hpR).ideal
    rw [Ideal.span_singleton_le_iff_mem]
    change psiRing P hpA P.generator ∈ Ideal.span {(p : WittVector p R)}
    let x := WittVector.map q (w P.generator)
    have hx : x.coeff 0 = 0 := by
      change q P.generator = 0
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
    let y := WittVector.mk p (fun n => x.coeff (n + 1))
    have h : verschiebung y = x := by
      ext n
      cases n with
      | zero => rw [verschiebung_coeff_zero, hx]
      | succ n => rfl
    change WittVector.frobenius x ∈ Ideal.span {(p : WittVector p R)}
    rw [← h, frobenius_verschiebung]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_singleton _))

end SerrePositivity.BhattScholze.Prismatic

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite BS19 "Thm 6.4" (partial := component) "Witt の結晶 prism と、普遍基底での比較の部品（BS-D69 P2）。関手としての同型（D69）の組み立ては drafts ／ 11-11 更新。Witt 系は A と A/I が p 正則な一般の有界向き付き prism について作られている ／ 11-12 夜更新（§5・§6 の見直し）"] _root_.SerrePositivity.BhattScholze.Prismatic.psiPrism
attribute [cite BS19 "Thm 6.4" (partial := component) "Witt の結晶 prism と、普遍基底での比較の部品（BS-D69 P2）。関手としての同型（D69）の組み立ては drafts ／ 11-11 更新。Witt 系は A と A/I が p 正則な一般の有界向き付き prism について作られている ／ 11-12 夜更新（§5・§6 の見直し）"] _root_.SerrePositivity.BhattScholze.Prismatic.wittCrystallineDelta
