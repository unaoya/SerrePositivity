module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.CrystallineCover.CrystallineCover
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.CrystallineCover.Construction61Frobenius
public import SerrePositivity.CommutativeAlgebra.Adic.RegularLift
public import SerrePositivity.BhattScholze.Delta.DividedPower.Frobenius.FrobeniusDivisionRegularSequence
public import SerrePositivity.BhattScholze.Delta.Division.Family

/-!
# Construction 6.1 の生の除算包の正則性

## 概要
A/d の p 正則性から、生の Frobenius 除算の p 正則性を得る。

## 方針
d 進分離性で A の p 正則性を得て、分冪包と δ 除算包の比較 の一元の場合に再添字付けする。

## 規約
BS 著者版 Construction 6.1、Corollary 2.39。完全性は prism から取る。

## 使われ方
ねじれ除去模型と原典の生の包の比較。
-/

public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u

namespace SerrePositivity.BhattScholze.Prismatic.Construction61

variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] (P : OrientedPrism p A)

/-- 概要：prism 商が p 正則なら係数環も p 正則。
方針：d の正則性と d 進分離性で剰余の正則性を持ち上げる。
規約：BS 著者版 Construction 6.1 の仮定。
使われ方：生の Frobenius 除算に 分冪包と δ 除算包の比較 を適用する。 -/
theorem prime_regular (hR : IsSMulRegular (A ⧸ P.ideal) (p : A ⧸ P.ideal)) :
    IsSMulRegular A (p : A) := by
  letI := P.isAdicComplete_generator
  apply isSMulRegular_of_quotient_of_isHausdorff P.generator (p : A) P.generator_regular
  simpa only [OrientedPrism.ideal, map_natCast] using hR

/-- 生の φ(d)/p の δ 除算環。 -/
abbrev coverRawDivision := DeltaAdjoinDivision P.deltaStructure (p : A)
  (fun _ : Unit => P.deltaStructure.frobeniusLift P.generator)

private def oneIndex : Unit ≃ Fin 1 where
  toFun := fun _ => 0
  invFun := fun _ => ()
  left_inv := fun _ => rfl
  right_inv := fun _ => Subsingleton.elim _ _

include P in
private theorem primeLocal (n : ℕ) (hn : ¬p ∣ n) : IsUnit (n : A) := by
  have hcop : Nat.Coprime n p := ((Nat.Prime.coprime_iff_not_dvd (Fact.out : p.Prime)).mpr hn).symm
  have hab := Nat.gcd_eq_gcd_ab n p
  rw [show Nat.gcd n p = 1 from hcop] at hab
  have ha : (1 : A) = (n : A) * (Nat.gcdA n p : A) + (p : A) * (Nat.gcdB n p : A) := by
    change (1 : ℤ) = _ at hab
    simpa only [Int.cast_one, Int.cast_add, Int.cast_mul, Int.cast_natCast] using
      congrArg (fun z : ℤ => (z : A)) hab
  have hu := (Ideal.mem_jacobson_bot.mp P.p_mem_jacobson) (-((Nat.gcdB n p : ℤ) : A))
  have he : (p : A) * -((Nat.gcdB n p : ℤ) : A) + 1 =
      (n : A) * ((Nat.gcdA n p : ℤ) : A) := by
    rw [mul_neg, ha]
    abel
  rw [he] at hu
  exact isUnit_of_mul_isUnit_left hu

/-- 概要：生の φ(d)/p の δ 除算でも p は正則。
方針：分冪包と δ 除算包の比較 の一元の Frobenius 除算へ再添字付けし、係数環と mod p の正則性を入力する。
規約：BS 著者版 Corollary 2.39、Construction 6.1。
使われ方：ねじれ除去商は生の包と同型であること。 -/
theorem coverRawDivision_p_regular
    (hR : IsSMulRegular (A ⧸ P.ideal) (p : A ⧸ P.ideal)) :
    IsSMulRegular (coverRawDivision P) (p : coverRawDivision P) := by
  have hmod : IsKoszulResolution
      (Ideal.Quotient.mk (Ideal.span {(p : A)}) ∘ (fun _ : Fin 1 => P.generator)) := by
    apply isKoszulResolution_of_isWeaklyRegular
    rw [show List.ofFn (Ideal.Quotient.mk (Ideal.span {(p : A)}) ∘
      (fun _ : Fin 1 => P.generator)) =
        [Ideal.Quotient.mk (Ideal.span {(p : A)}) P.generator] by simp [List.ofFn_succ]]
    exact (RingTheory.Sequence.isWeaklyRegular_singleton_iff _ _).mpr
      (generator_modP_regular P hR)
  have hreg := frobeniusDivision_primeRegular P.deltaStructure (primeLocal P)
    (fun _ : Fin 1 => P.generator) (prime_regular P hR) hmod
  let e := deltaAdjoinDivisionReindexEquiv P.deltaStructure (p : A)
    (fun _ : Unit => P.deltaStructure.frobeniusLift P.generator)
    (fun _ : Fin 1 => P.deltaStructure.frobeniusLift P.generator) oneIndex (fun _ => rfl)
  intro x y hxy
  apply e.injective
  apply hreg
  change (p : _) * e x = (p : _) * e y
  simpa only [smul_eq_mul, map_mul, map_natCast] using congrArg e hxy

set_option maxHeartbeats 1200000 in
/-- 概要：生の一元除算包と分冪表示の係数上の標準同型。
方針：Unit を Fin 1 に再添字付けして 分冪包と δ 除算包の比較 の標準同型を使う。
規約：BS 著者版 Corollary 2.39、Construction 6.1。
使われ方：被覆の mod p の分冪表示。 -/
def coverRawDPFamilyEquiv :
    coverRawDivision P ≃ₐ[A] DPFamilyPresentation (fun _ : Fin 1 => P.generator) := by
  let eIndex : Unit ≃ Fin 1 :=
    ⟨fun _ => 0, fun _ => (), fun _ => rfl, fun _ => Subsingleton.elim _ _⟩
  let e := deltaAdjoinDivisionReindexEquiv P.deltaStructure (p : A)
    (fun _ : Unit => P.deltaStructure.frobeniusLift P.generator)
    (fun _ : Fin 1 => P.deltaStructure.frobeniusLift P.generator) eIndex (fun _ => rfl)
  have heA (a : A) : e (deltaAdjoinDivisionMap P.deltaStructure (p : A)
      (fun _ : Unit => P.deltaStructure.frobeniusLift P.generator) a) =
      deltaAdjoinDivisionMap P.deltaStructure (p : A)
        (fun _ : Fin 1 => P.deltaStructure.frobeniusLift P.generator) a :=
    DFunLike.congr_fun (deltaAdjoinDivisionReindexEquiv_comp P.deltaStructure (p : A)
      (fun _ : Unit => P.deltaStructure.frobeniusLift P.generator)
      (fun _ : Fin 1 => P.deltaStructure.frobeniusLift P.generator) eIndex (fun _ => rfl)) a
  let eA : coverRawDivision P ≃ₐ[A]
      DeltaAdjoinDivision P.deltaStructure (p : A)
        (fun _ : Fin 1 => P.deltaStructure.frobeniusLift P.generator) :=
    { __ := e, commutes' := heA }
  exact eA.trans (frobeniusDivisionDPFamilyEquiv P.deltaStructure (primeLocal P)
    (fun _ : Fin 1 => P.generator))

/-- 概要：p 正則な生の包のねじれ除去イデアルは零。
方針：恒等 δ 射が正則な p を保つので、その核にねじれ除去イデアルが入る。
規約：BS 著者版 Construction 6.1 の二つの模型の比較。
使われ方：商の同型と係数脚の照合。 -/
theorem coverRawDivision_torsionIdeal_eq_bot
    (hR : IsSMulRegular (A ⧸ P.ideal) (p : A ⧸ P.ideal)) :
    (deltaAdjoinDivisionStructure P.deltaStructure (p : A)
      (fun _ : Unit => P.deltaStructure.frobeniusLift P.generator)).deltaClosure
        (RingHom.ker (algebraMap (coverRawDivision P)
          (Localization.Away (deltaAdjoinDivisionMap P.deltaStructure (p : A)
            (fun _ : Unit => P.deltaStructure.frobeniusLift P.generator) (p : A))))) = ⊥ := by
  apply le_antisymm _ bot_le
  have hreg : Function.Injective (fun x : coverRawDivision P =>
      (RingHom.id (coverRawDivision P))
        (deltaAdjoinDivisionMap P.deltaStructure (p : A)
          (fun _ : Unit => P.deltaStructure.frobeniusLift P.generator) (p : A)) * x) := by
    have hh := coverRawDivision_p_regular P hR
    change Function.Injective (fun x : coverRawDivision P => (p : coverRawDivision P) * x) at hh
    simpa only [RingHom.id_apply, map_natCast] using hh
  have hle :=
    (deltaAdjoinDivisionStructure P.deltaStructure (p : A)
      (fun _ : Unit => P.deltaStructure.frobeniusLift P.generator)).isDeltaHom_id.deltaClosure_ker_away_le_ker
      (deltaAdjoinDivisionMap P.deltaStructure (p : A)
        (fun _ : Unit => P.deltaStructure.frobeniusLift P.generator) (p : A)) hreg
  intro x hx
  exact hle hx

/-- 概要：ねじれ除去した模型は原典の生の除算包と標準同型。
方針：除去イデアルが零なので零イデアル商と同定する。
規約：BS 著者版 Construction 6.1。A/d の p 正則性を明示する。
使われ方：生の分冪表示と完備化の還元比較。 -/
def coverDivisionRawEquiv
    (hR : IsSMulRegular (A ⧸ P.ideal) (p : A ⧸ P.ideal)) :
    coverDivision P ≃+* coverRawDivision P :=
  (Ideal.quotEquivOfEq (coverRawDivision_torsionIdeal_eq_bot P hR)).trans
    (RingEquiv.quotientBot _)

/-- 生の包との同型は A の係数を保つ。 -/
theorem coverDivisionRawEquiv_base
    (hR : IsSMulRegular (A ⧸ P.ideal) (p : A ⧸ P.ideal)) (a : A) :
    coverDivisionRawEquiv P hR (coverDivisionMap P a) =
      deltaAdjoinDivisionMap P.deltaStructure (p : A)
        (fun _ : Unit => P.deltaStructure.frobeniusLift P.generator) a := by
  simp only [coverDivisionRawEquiv, coverDivisionMap, deltaDivisionTorsionMap,
    RingHom.comp_apply, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
    RingEquiv.quotientBot_mk]

end SerrePositivity.BhattScholze.Prismatic.Construction61
