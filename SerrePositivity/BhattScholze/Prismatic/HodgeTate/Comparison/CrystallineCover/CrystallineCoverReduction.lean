module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.CrystallineCover.CrystallineCoverRegularity
public import SerrePositivity.BhattScholze.Delta.DividedPower.RegularSequence.RegularSequencePDReduction
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.RepeatedCoordinateResidue

/-!
# Construction 6.1 の結晶被覆の mod p

## 概要
被覆の mod p を、A/p の d に沿う分冪表示と標準係数脚を保って同定する。

## 方針
完備化、ねじれ除去商、生の除算と分冪表示の比較を順に合成する。

## 規約
BS 著者版 Construction 6.1、式 (6)。A/d の p 正則性を明示する。

## 使われ方
式 (6) の忠実性と Tor 振幅。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
namespace SerrePositivity.BhattScholze.Prismatic.Construction61
open DerivedCompletion

variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] (P : OrientedPrism p A)

/-- 剰余環上の一元分冪表示。 -/
abbrev coverPDResidue := DPFamilyPresentation
  (fun _ : Fin 1 => Ideal.Quotient.mk (Ideal.span {(p : A)}) P.generator)

/-- 概要：結晶被覆の mod p は元の族の分冪表示の mod p。
方針：完備化の mod p と 分冪包と δ 除算包の比較 の同型を標準脚に沿って合成する。
規約：BS 著者版 Construction 6.1 の式 (6) の標的。
使われ方：剰余底変換の忠実性と次数の評価。 -/
def coverModPEquiv
    (hR : IsSMulRegular (A ⧸ P.ideal) (p : A ⧸ P.ideal)) :
    ModP (crystallineCoverRing P) p ≃+* coverPDResidue P := by
  let e := coverDivisionRawEquiv P hR
  let t := (coverRawDPFamilyEquiv P).toRingEquiv
  let e₀ := Ideal.quotientEquiv
    (Ideal.span {(p : coverDivision P)}) (Ideal.span {(p : coverRawDivision P)}) e (by
      rw [Ideal.map_span, Set.image_singleton, map_natCast])
  let t₀ := Ideal.quotientEquiv
    (Ideal.span {(p : coverRawDivision P)})
    (Ideal.span {(p : DPFamilyPresentation (fun _ : Fin 1 => P.generator))}) t (by
      rw [Ideal.map_span, Set.image_singleton, map_natCast])
  exact (repeatedCompletionModPEquiv (coverDivision P) p).trans
    (e₀.trans (t₀.trans (dpFamilyModPrimeEquiv p (fun _ : Fin 1 => P.generator))))

/-- 概要：被覆の剰余同型は A からの自然な係数脚を保つ。
方針：各比較の標準係数上の公式を順に使う。
規約：BS 著者版 Construction 6.1 の自然な A 代数構造。
使われ方：Frobenius で捻った α の因数分解。 -/
theorem coverModPEquiv_base
    (hR : IsSMulRegular (A ⧸ P.ideal) (p : A ⧸ P.ideal)) (a : A) :
    coverModPEquiv P hR (Ideal.Quotient.mk _ (coverBase P a)) =
      algebraMap (ModP A p) (coverPDResidue P) (Ideal.Quotient.mk _ a) := by
  change coverModPEquiv P hR
    (Ideal.Quotient.mk _ (pdCompletionUnit (coverDivision P) p (p : coverDivision P)
      (coverDivisionMap P a))) = _
  unfold coverModPEquiv
  rw [RingEquiv.trans_apply]
  rw [repeatedCompletionModPEquiv_unit]
  simp only [RingEquiv.trans_apply, Ideal.quotientEquiv_mk, coverDivisionRawEquiv_base]
  change dpFamilyModPrimeEquiv p (fun _ : Fin 1 => P.generator)
    (Ideal.Quotient.mk _ (coverRawDPFamilyEquiv P
      (algebraMap A (coverRawDivision P) a))) = _
  rw [AlgEquiv.commutes, dpFamilyModPrimeEquiv_coeff]
  rfl

/-- α に沿う通常の mod p の環射。 -/
abbrev alphaModP : ModP A p →+* ModP (crystallineCoverRing P) p :=
  modPMap p (crystallineCoverMap P).toRingHom

/-- 概要：剰余比較を通した α は係数の p 乗を取る。
方針：自然な係数脚の公式と mod p の Frobenius の値を合わせる。
規約：BS 著者版 Construction 6.1 の式 (6) の合成射。
使われ方：Frobenius 剰余と分冪表示への係数脚の分解。 -/
theorem coverModPEquiv_alpha
    (hR : IsSMulRegular (A ⧸ P.ideal) (p : A ⧸ P.ideal)) (a : ModP A p) :
    coverModPEquiv P hR (alphaModP P a) =
      algebraMap (ModP A p) (coverPDResidue P) (a ^ p) := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  change coverModPEquiv P hR
    (Ideal.Quotient.mk _ (coverBase P (P.deltaStructure.frobeniusLift a))) = _
  rw [coverModPEquiv_base]
  exact congrArg (algebraMap (ModP A p) (coverPDResidue P))
    (modPFrobenius_apply P (Ideal.Quotient.mk _ a))

end SerrePositivity.BhattScholze.Prismatic.Construction61
