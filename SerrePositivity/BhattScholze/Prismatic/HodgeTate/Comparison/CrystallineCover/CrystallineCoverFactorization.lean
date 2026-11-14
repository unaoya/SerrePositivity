module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.CrystallineCover.CrystallineCoverReduction
public import SerrePositivity.BhattScholze.Delta.DividedPower.RegularSequence.RegularSequencePDTruncatedFlat
public import SerrePositivity.HomologicalAlgebra.KoszulTorBound
public import SerrePositivity.HomologicalAlgebra.TorPostFlatComposition

/-!
# Construction 6.1 の式 (6)

## 概要
被覆の mod p の標準射を、正則主元の商、忠実平坦な Frobenius 剰余、分冪表示の係数射へ分解する。

## 方針
分冪包と δ 除算包の比較 の切断分冪基底と Construction 6.1 の Frobenius 入力を、係数脚の比較で接続する。

## 規約
BS 著者版 Construction 6.1 の式 (6)。

## 使われ方
mod p の Tor 次元と、完備な底変換の保存性。
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
namespace SerrePositivity.BhattScholze.Prismatic.Construction61

variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] (P : OrientedPrism p A)

/-- 剰余環の選択した生成元。 -/
abbrev coverModPGenerator : ModP A p := Ideal.Quotient.mk (Ideal.span {(p : A)}) P.generator

private theorem modP_prime_zero : (p : ModP A p) = 0 := by
  simpa only [map_natCast] using
    (Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self (p : A)))

private theorem coefficientIdeal_eq :
    (truncatedPolynomialIdeal (ModP A p) (Fin 1) p).map
      (MvPolynomial.aeval (fun _ : Fin 1 => coverModPGenerator P)).toRingHom =
        Ideal.span {(coverModPGenerator P) ^ p} := by
  rw [truncatedPolynomialIdeal, Ideal.map_span, ← Set.range_comp']
  congr 1
  ext z
  simp [Function.comp_def]

private def coefficientQuotientEquiv :
    DPTruncatedCoefficientQuotient (p := p) (fun _ : Fin 1 => coverModPGenerator P) ≃+*
      (ModP A p ⧸ Ideal.span {(coverModPGenerator P) ^ p}) :=
  Ideal.quotEquivOfEq (coefficientIdeal_eq P)

/-- 分冪表示への式 (6) の最後の係数射。 -/
def coverPDResidueCoefficientMap :
    (ModP A p ⧸ Ideal.span {(coverModPGenerator P) ^ p}) →+* coverPDResidue P :=
  (dpTruncatedCoefficientMap (fun _ : Fin 1 => coverModPGenerator P) (modP_prime_zero (A := A))).comp
    (coefficientQuotientEquiv P).symm.toRingHom

/-- 係数射は元の係数を保つ。 -/
theorem coverPDResidueCoefficientMap_mk (a : ModP A p) :
    coverPDResidueCoefficientMap P (Ideal.Quotient.mk _ a) =
      algebraMap (ModP A p) (coverPDResidue P) a := by
  have hq : (coefficientQuotientEquiv P).symm (Ideal.Quotient.mk _ a) =
      Ideal.Quotient.mk _ a := by
    apply (coefficientQuotientEquiv P).injective
    rw [RingEquiv.apply_symm_apply]
    exact (Ideal.quotEquivOfEq_mk (coefficientIdeal_eq P) a).symm
  change dpTruncatedCoefficientMap (fun _ : Fin 1 => coverModPGenerator P)
    (modP_prime_zero (A := A)) ((coefficientQuotientEquiv P).symm
      (Ideal.Quotient.mk _ a)) = _
  exact (congrArg (dpTruncatedCoefficientMap (fun _ : Fin 1 => coverModPGenerator P)
    (modP_prime_zero (A := A))) hq).trans
      (dpTruncatedCoefficientMap_mk (fun _ : Fin 1 => coverModPGenerator P)
        (modP_prime_zero (A := A)) a)

/-- 概要：分冪表示の係数射は忠実平坦。
方針：分冪包と δ 除算包の比較 の切断多項式上の自由性の底変換を係数商の同型で移す。
規約：BS 著者版 Construction 6.1 の式 (6) の最後の射。
使われ方：被覆の剰余による消滅の検出。 -/
theorem coverPDResidueCoefficientMap_faithfullyFlat :
    (coverPDResidueCoefficientMap P).FaithfullyFlat :=
  RingHom.FaithfullyFlat.stableUnderComposition _ _
    (RingHom.FaithfullyFlat.of_bijective (coefficientQuotientEquiv P).symm.bijective)
    (dpTruncatedCoefficientMap_faithfullyFlat _ (modP_prime_zero (A := A)))

/-- 被覆の実際の mod p を標的とする最後の射。 -/
def coverResidueFlatMap
    (hR : IsSMulRegular (A ⧸ P.ideal) (p : A ⧸ P.ideal)) :
    (ModP A p ⧸ Ideal.span {(coverModPGenerator P) ^ p}) →+* ModP (crystallineCoverRing P) p :=
  (coverModPEquiv P hR).symm.toRingHom.comp (coverPDResidueCoefficientMap P)

/-- 概要：実際の被覆の剰余への最後の射は忠実平坦。
方針：分冪表示の忠実平坦性を標準比較同型で移す。
規約：BS 著者版 Construction 6.1 の式 (6)。
使われ方：保存性と Tor 振幅。 -/
theorem coverResidueFlatMap_faithfullyFlat
    (hR : IsSMulRegular (A ⧸ P.ideal) (p : A ⧸ P.ideal)) :
    (coverResidueFlatMap P hR).FaithfullyFlat :=
  RingHom.FaithfullyFlat.stableUnderComposition _ _ (coverPDResidueCoefficientMap_faithfullyFlat P)
    (RingHom.FaithfullyFlat.of_bijective (coverModPEquiv P hR).symm.bijective)

/-- 概要：実際の α の mod p は式 (6) の三射の合成。
方針：標準剰余比較を適用し、係数の p 乗で両辺を同定する。
規約：BS 著者版 Construction 6.1 の原典の標準脚。
使われ方：Tor 次元と完備 Nakayama による保存性。 -/
theorem alphaModP_factorization
    (hR : IsSMulRegular (A ⧸ P.ideal) (p : A ⧸ P.ideal)) :
    alphaModP P = ((coverResidueFlatMap P hR).comp (residueFrobenius P)).comp
      (Ideal.Quotient.mk (Ideal.span {coverModPGenerator P})) := by
  apply RingHom.ext
  intro a
  apply (coverModPEquiv P hR).injective
  simp only [RingHom.comp_apply]
  rw [coverModPEquiv_alpha]
  simp only [coverResidueFlatMap, RingHom.comp_apply,
    RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply]
  rw [Frobenius.principalQuotientMap_mk, coverPDResidueCoefficientMap_mk,
    modPFrobenius_apply]

/-- 概要：被覆の mod p の通常の Tor 次元は高々一。
方針：式 (6) の最初は正則主元の商で、後の二射は平坦。
規約：BS 著者版 Construction 6.1、Construction 6.1。任意の係数加群。
使われ方：非有界な鎖複体の模型に対する次数評価の入力。 -/
theorem torAmplitude_modP_le_one
    (hF : IsCompletelyFlat (Ideal.span {coverModPGenerator P})
      (baseChangeScalarModule (modPMap p P.deltaStructure.frobeniusLift)))
    (hR : IsSMulRegular (A ⧸ P.ideal) (p : A ⧸ P.ideal))
    (M : ModuleCat.{u} (ModP A p)) (i : ℕ) (hi : 1 < i) :
    Subsingleton (TorAlg (alphaModP P) i M) := by
  rw [alphaModP_factorization P hR]
  apply torAlg_subsingleton_postcomp_flat
    (Ideal.Quotient.mk (Ideal.span {coverModPGenerator P}))
    ((coverResidueFlatMap P hR).comp (residueFrobenius P))
    ((residueFrobenius_faithfullyFlat P hF).flat.comp
      (coverResidueFlatMap_faithfullyFlat P hR).flat)
  exact torAlg_principalQuotient_subsingleton_of_one_lt _ (generator_modP_regular P hR) M i hi

end SerrePositivity.BhattScholze.Prismatic.Construction61
