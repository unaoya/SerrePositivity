module

public import SerrePositivity.BhattScholze.Prismatic.CechAlexander.Frames.AffineCechFrameLift
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.WittBigBridgeAffineFrame
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.WittSmallFrame
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.WittSmallFrame
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDSmallModelComparison
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDCechNerve
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.Comparison.PDFrobeniusLift

/-!
# 有限枠に対する Witt の結晶の橋

## 概要
有限 prismatic 枠から有限 Witt 分冪枠への環射を各次数で構成する。

## 方針
分冪イデアルに入る頂点差の p 乗は p で割り切れる。
各頂点の変数の p 乗を指定し、有限 prismatic 包の普遍性を適用する。

## 規約
係数の射は ψ。剰余係数環は p 正則かつ p 完備。

## 使われ方
BS 著者版 Theorem 6.4 の結晶の橋の有限枠での計算。
-/

public noncomputable section

open CategoryTheory SerrePositivity.DerivedCompletion
open scoped Simplicial

universe u

namespace SerrePositivity.BhattScholze.Prismatic.WittFiniteBridge

set_option backward.isDefEq.respectTransparency false

variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] (P : OrientedPrism p A)
variable (hpA : Function.Injective (fun x : A => (p : A) * x))
variable (hpC : Function.Injective (fun x : A ⧸ P.ideal => (p : A ⧸ P.ideal) * x))
variable (hloc : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A ⧸ P.ideal))
variable (hk : IsAdicComplete (Ideal.span {(p : A ⧸ P.ideal)}) (A ⧸ P.ideal))
variable (Q : Poly (A ⧸ P.ideal)) (n : ℕ)

local notation "C" => (A ⧸ P.ideal)
local notation "W" => WittVector p C
local notation "γ" => wittPdStructure p C hpC hloc
local notation "hpW" => p_mem_wittPdIdeal p C
local notation "D" => PDCechNerve.term p γ hpW (smallResidue_ker P Q) (smallFrame P Q) n

include hk in
private theorem regular : Function.Injective (fun x : (D).carrier => (p : (D).carrier) * x) := by
  let wreg := witt_mul_prime_injective p C hpC
  let e := PDSmallModelComparison.termEquiv p W γ hpW (wittComplete P hpC hk) wreg
    Q.n (smallResidue_ker P Q) n
  intro a b h
  apply e.symm.injective
  have h' := congrArg (fun x : (D).carrier => e.symm x) h
  simp only [map_mul, map_natCast] at h'
  apply principalCompletionH0_smul_injective_of_regular (pdRaw W Q.n n)
    (p : pdRaw W Q.n n) (PDSmallRawEnvelope.raw_regular p Q.n n wreg)
  have h'' : p • (e.symm a : pdTerm p W Q.n n) = p • (e.symm b : pdTerm p W Q.n n) := by
    rw [nsmul_eq_mul, nsmul_eq_mul]
    exact h'
  simpa only [Nat.cast_smul_eq_nsmul] using h''

local notation "T" => wittPDEnvelopeCrystalline hpC hloc D (regular P hpC hloc hk Q n)
local notation "b" => OrientedPrism.Hom.comp (wittPDEnvelopeCrystallineBase hpC hloc D
  (regular P hpC hloc hk Q n)) (psiPrism P hpA hpC)

private abbrev variableImage (j : Fin Q.n) (i : Fin (n + 1)) : (D).carrier :=
  (D).unit (MvPolynomial.X (ULift.up j, i))

private theorem variable_diff_mem (j : Fin Q.n) (i : Fin (n + 1)) :
    variableImage P hpC hloc Q n j i - variableImage P hpC hloc Q n j 0 ∈ (D).ideal := by
  let e := PDCechNerve.augmentation p γ hpW (smallResidue_ker P Q) (smallFrame P Q) n
  rw [← PDCechNerve.augmentation_ker]
  apply RingHom.mem_ker.mpr
  change e (variableImage P hpC hloc Q n j i - variableImage P hpC hloc Q n j 0) = 0
  rw [map_sub]
  change e (PDCechNerve.variableImage p γ hpW (smallResidue_ker P Q) (smallFrame P Q) n
    (ULift.up j, i)) - e (PDCechNerve.variableImage p γ hpW (smallResidue_ker P Q)
      (smallFrame P Q) n (ULift.up j, 0)) = 0
  rw [PDCechNerve.augmentation_variableImage, PDCechNerve.augmentation_variableImage, sub_self]

private theorem powers_mod (j : Fin Q.n) (i : Fin (n + 1)) :
    Ideal.Quotient.mk (T).ideal (variableImage P hpC hloc Q n j i ^ p) =
      Ideal.Quotient.mk (T).ideal (variableImage P hpC hloc Q n j 0 ^ p) := by
  have hI : (T).ideal = Ideal.span {(p : (D).carrier)} := by
    change Ideal.span {(T).generator} = _
    rw [wittPDEnvelopeCrystalline_generator]
  rw [hI]
  let q := Ideal.Quotient.mk (Ideal.span {(p : (D).carrier)})
  have hzero : (p : (D).carrier ⧸ Ideal.span {(p : (D).carrier)}) = 0 := by
    rw [← map_natCast q]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  let F := (frobeniusOfPrimeZero hzero).comp q
  have h := RingHom.mem_ker.mp (frobenius_ideal_le_ker γ D
    (variable_diff_mem P hpC hloc Q n j i))
  change F (variableImage P hpC hloc Q n j i - variableImage P hpC hloc Q n j 0) = 0 at h
  rw [map_sub, sub_eq_zero] at h
  simpa only [F, RingHom.comp_apply, frobeniusOfPrimeZero, RingHom.coe_mk, MonoidHom.coe_mk,
    OneHom.coe_mk, map_pow] using h

variable [IsAdicComplete (Ideal.span {(p : A ⧸ P.ideal)}) (A ⧸ P.ideal)]
variable {κ : Cardinal.{u}} (X : AffineEnvelopeTerm P Q.n n κ)

private theorem existsUnique_at :
    ∃! f : X.X.B →+* (D).carrier,
      X.X.Q.deltaStructure.IsDeltaHom (T).deltaStructure f ∧
      f.comp X.X.toHom.toRingHom = (b).toRingHom ∧
      ∀ j i, f (X.η (affineVariable P Q.n n j i)) = variableImage P hpC hloc Q n j i ^ p :=
  X.existsUnique_liftVariables (T) (b) (fun j i => variableImage P hpC hloc Q n j i ^ p)
    (powers_mod P hpC hloc hk Q n)

/-- 有限 prismatic 枠から小さい Witt 模型の完備項への結晶の橋。 -/
def finiteBridgeAt : X.X.B →+* pdTerm p W Q.n n :=
  let e := PDSmallModelComparison.termEquiv p W γ hpW (wittComplete P hpC hk)
    (witt_mul_prime_injective p C hpC) Q.n (smallResidue_ker P Q) n
  e.symm.toRingHom.comp (existsUnique_at P hpA hpC hloc hk Q n X).choose

end SerrePositivity.BhattScholze.Prismatic.WittFiniteBridge
