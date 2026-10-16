module

public import SerrePositivity.BhattScholze.PerfectDeltaWittRecovery
public import SerrePositivity.BhattScholze.PerfectOrientedPrism
public import Mathlib.RingTheory.AdicCompletion.Topology

/-! # 完全oriented prismの標準Witt表示

既存のWitt復元同型と選択生成元をそのまま使い、主イデアルと標準商を比較する。
環・商の比較は零環を含む。標準Witt δ構造との両立にはmod p環のCharPを明示する。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]
variable (P : OrientedPrism p A) (hP : P.deltaStructure.IsPerfect)

/-- 完全prismのp完備性を供給した、既存のWitt復元同型そのもの。 -/
abbrev perfectPrismWittRecoveryEquiv : WittVector p (ModP A p) ≃+* A :=
  letI := P.isAdicComplete_p_of_perfect hP
  perfectDeltaWittRecoveryEquiv P.deltaStructure hP

/-- 同じ復元同型の逆像として定める、選択済みprism生成元のWitt表示。 -/
abbrev perfectPrismWittGenerator : WittVector p (ModP A p) :=
  (perfectPrismWittRecoveryEquiv P hP).symm P.generator

/-- Witt表示の生成元は、元の選択生成元へ写る。 -/
@[simp] theorem perfectPrismWittRecoveryEquiv_generator :
    perfectPrismWittRecoveryEquiv P hP (perfectPrismWittGenerator P hP) = P.generator :=
  (perfectPrismWittRecoveryEquiv P hP).apply_symm_apply _

/-- Witt生成元の主イデアルの像は、元のprismイデアル。 -/
theorem perfectPrismWittGenerator_map_span :
    (Ideal.span {perfectPrismWittGenerator P hP}).map
      (perfectPrismWittRecoveryEquiv P hP).toRingHom = P.ideal := by
  simp only [Ideal.map_span, Set.image_singleton]
  change Ideal.span {perfectPrismWittRecoveryEquiv P hP (perfectPrismWittGenerator P hP)} =
    Ideal.span {P.generator}
  rw [perfectPrismWittRecoveryEquiv_generator]

/-- 逆方向にも、元のprismイデアルは同じWitt生成元の主イデアルへ写る。 -/
theorem perfectPrismWittRecoveryEquiv_symm_map_ideal :
    P.ideal.map (perfectPrismWittRecoveryEquiv P hP).symm.toRingHom =
      Ideal.span {perfectPrismWittGenerator P hP} := by
  simp only [OrientedPrism.ideal, Ideal.map_span, Set.image_singleton]
  rfl

/-- 同じWitt環は、復元した生成元について古典的完備。 -/
theorem perfectPrismWitt_isAdicComplete_generator :
    IsAdicComplete (Ideal.span {perfectPrismWittGenerator P hP}) (WittVector p (ModP A p)) := by
  have h := (IsAdicComplete.congr_ringEquiv P.ideal
    (perfectPrismWittRecoveryEquiv P hP).symm).mpr P.isAdicComplete_generator
  change IsAdicComplete
    (P.ideal.map (perfectPrismWittRecoveryEquiv P hP).symm.toRingHom) (WittVector p (ModP A p)) at h
  simpa only [perfectPrismWittRecoveryEquiv_symm_map_ideal] using h

/-- 同じ復元環同型から誘導される、Witt主イデアル商と元のprism商の比較。 -/
def perfectPrismWittQuotientEquiv :
    WittVector p (ModP A p) ⧸ Ideal.span {perfectPrismWittGenerator P hP} ≃+* A ⧸ P.ideal :=
  Ideal.quotientEquiv _ _ (perfectPrismWittRecoveryEquiv P hP)
    (perfectPrismWittGenerator_map_span P hP).symm

/-- 商比較は元のWitt元の標準商像を保つ。 -/
@[simp] theorem perfectPrismWittQuotientEquiv_mk (x : WittVector p (ModP A p)) :
    perfectPrismWittQuotientEquiv P hP (Ideal.Quotient.mk _ x) =
      Ideal.Quotient.mk P.ideal (perfectPrismWittRecoveryEquiv P hP x) := rfl

/-- 商比較の逆射も、元の環の標準商像に関する公式を持つ。 -/
@[simp] theorem perfectPrismWittQuotientEquiv_symm_mk (a : A) :
    (perfectPrismWittQuotientEquiv P hP).symm (Ideal.Quotient.mk P.ideal a) =
      Ideal.Quotient.mk _ ((perfectPrismWittRecoveryEquiv P hP).symm a) := rfl

section DeltaCompatibility
variable [CharP (ModP A p) p]

/-- mod p環が標数pを持つ場合、同じ復元同型は標準Witt δ構造と両立する。 -/
theorem perfectPrismWittRecoveryEquiv_isDeltaHom :
    letI := hP.perfectRing_mod_p
    (wittDeltaStructure p (ModP A p)).IsDeltaHom P.deltaStructure
      (perfectPrismWittRecoveryEquiv P hP).toRingHom := by
  let := hP.perfectRing_mod_p
  let := P.isAdicComplete_p_of_perfect hP
  exact perfectDeltaWittRecoveryEquiv_isDeltaHom P.deltaStructure hP

/-- 逆方向の復元同型も同じ標準Witt δ構造と両立する。 -/
theorem perfectPrismWittRecoveryEquiv_symm_isDeltaHom :
    letI := hP.perfectRing_mod_p
    P.deltaStructure.IsDeltaHom (wittDeltaStructure p (ModP A p))
      (perfectPrismWittRecoveryEquiv P hP).symm.toRingHom := by
  let := hP.perfectRing_mod_p
  let := P.isAdicComplete_p_of_perfect hP
  exact perfectDeltaWittRecoveryEquiv_symm_isDeltaHom P.deltaStructure hP

/-- 選択生成元のWitt表示は、標準Witt δ構造についてdistinguished。 -/
theorem perfectPrismWittGenerator_isDistinguished :
    letI := hP.perfectRing_mod_p
    (wittDeltaStructure p (ModP A p)).IsDistinguished (perfectPrismWittGenerator P hP) := by
  let := hP.perfectRing_mod_p
  exact (perfectPrismWittRecoveryEquiv_symm_isDeltaHom P hP).map_isDistinguished
    (P.isDistinguished_of_perfect hP)

end DeltaCompatibility
end SerrePositivity.BhattScholze
