module

public import SerrePositivity.AlgebraicGeometry.CompactMinimalPrimeIntegralExtension
public import SerrePositivity.AlgebraicGeometry.AffineVCoverNilImmersion
public import SerrePositivity.AlgebraicGeometry.SchemeVCoverSurjective
public import Mathlib.RingTheory.Nilpotent.Lemmas
public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
概要：C01 を被約化と合成し、任意の環の整全射の被約な拡大を取る。
方針：nilradical による商の後に C01 の単射整拡大を取り、整性と Spec の全射性を合成する。
規約：元の環の被約性・新しい環への写像の単射性は要求しない。
使われ方：A07 の一般の affine 基底への帰着。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory
universe u

/-- 任意の環は、被約かつ極小素点集合が準コンパクトな環から整全射で覆われる。 -/
theorem exists_integral_surjective_reduced_compact_minimalPrimes (R : CommRingCat.{u}) :
    ∃ (B : CommRingCat.{u}) (g : R →+* B), IsReduced B ∧ g.IsIntegral ∧
      Surjective (Spec.map (CommRingCat.ofHom g)) ∧
      IsCompact {q : PrimeSpectrum B | q.asIdeal ∈ minimalPrimes B} := by
  let A := R ⧸ nilradical R
  letI : IsReduced A := by
    apply (RingHom.ker_isRadical_iff_reduced_of_surjective
      (f := Ideal.Quotient.mk (nilradical R)) Ideal.Quotient.mk_surjective).mp
    rw [Ideal.mk_ker]
    exact Ideal.radical_isRadical 0
  obtain ⟨B, i, hB, hinj, hi, hmin⟩ :=
    exists_integral_injective_reduced_compact_minimalPrimes (CommRingCat.of A)
  let q : R →+* A := Ideal.Quotient.mk (nilradical R)
  have hq : q.IsIntegral := q.isIntegral_of_surjective Ideal.Quotient.mk_surjective
  haveI : Surjective (Spec.map (CommRingCat.ofHom i)) := ⟨hi.comap_surjective hinj⟩
  have hnil : IsSchemeVCover (Spec.map (CommRingCat.ofHom q)) :=
    (isSchemeVCover_specMap_iff _).mpr
      (isAffineVCover_quotient_of_le_nilradical (nilradical R) le_rfl)
  haveI : Surjective (Spec.map (CommRingCat.ofHom q)) := hnil.surjective
  refine ⟨B, i.comp q, hB, hq.trans _ _ hi, ?_, hmin⟩
  change Surjective (Spec.map (CommRingCat.ofHom q ≫ CommRingCat.ofHom i))
  rw [Spec.map_comp]
  infer_instance

end SerrePositivity.AlgebraicGeometry
