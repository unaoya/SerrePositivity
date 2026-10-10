module

public import SerrePositivity.LengthAlgebra.PerfectLowerBound
public import SerrePositivity.PerfectComplex.MinimalLowerBound

/-! # 有限射影版の極小性と Euler 下界 -/

@[expose] public section

universe u

set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.LengthAlgebra

open CategoryTheory CategoryTheory.Limits

variable {R : Type u} [CommRing R] {J : Ideal R} (lam : NormalizedLength R J)
  (hfg : J.FG) {e : ℕ} (z : Fin e → R)
  (hJ : J ≤ (Ideal.span (Set.range z)).radical) (hfin : KoszulFinite lam z)

/-- 第零次以外の長さが零なら、共通の Euler 評価は第零ホモロジーの長さ。 -/
lemma perfectEuler_eq_length_zero
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (hP : strictlyPerfectComplex R P)
    (hs : IsSupported z P) (hz : ∀ q : ℤ, q ≠ 0 → lam.len (P.homology q) = 0) :
    perfectEuler lam hfg z hJ hfin
      ⟨perfectHomotopyObj R P hP, (perfectHomotopyObj_supported_iff z P hP).mpr hs⟩ =
        (lam.len (P.homology 0)).toReal := by
  let X : SupportedPerfectHomotopy z :=
    ⟨perfectHomotopyObj R P hP, (perfectHomotopyObj_supported_iff z P hP).mpr hs⟩
  rw [perfectEuler, homologicalEuler_eq_length_zero (quotientLength lam)
    (perfectQuotientHomology lam hfg z hJ hfin 0)
    (fun Y hY ↦ (quotientLength_eq_zero_iff lam Y).mpr hY) X
    (fun q hq ↦ (perfectQuotientHomology_isZero_of_len_eq_zero lam hfg z hJ hfin
      P hP hs q (hz q hq)).of_iso
        ((perfectQuotientHomologyShiftIso lam hfg z hJ hfin q).app X))]
  exact (quotientLength_iso lam
    ((perfectQuotientHomologyShiftIso lam hfg z hJ hfin 0).app X)).trans
      (perfectQuotientHomology_length lam hfg z hJ hfin P hP hs 0)

/-- 有限射影複体の極小性から得られる Euler 下界。
消滅は共通の反復錐定理、下界は零次項から実際に構成した全射による。 -/
theorem perfectEuler_minimal_lower_bound
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (hP : strictlyPerfectComplex R P)
    (hs : IsSupported z P) (v : ℕ)
    (hx : ∀ j, Nonempty (Homotopy (smulId (z j ^ v) P) 0))
    (hzero : ∀ i : ℕ, 0 < i → lam.len (koszulHomologySelf (fun j ↦ z j ^ v) i) = 0)
    (hbound : ∀ q, q < -(e : ℤ) ∨ 0 < q → IsZero (P.X q))
    (I : Ideal R) (hI : IsPowTorsion J (R ⧸ I))
    (b : ℕ) (basis : P.X 0 ≅ ModuleCat.of R (Fin b → R))
    (hmin : ∀ m : P.X (-1), ∀ j, basis.hom.hom ((P.d (-1) 0).hom m) j ∈ I) :
    b * (lam.len (R ⧸ I)).toReal ≤ perfectEuler lam hfg z hJ hfin
      ⟨perfectHomotopyObj R P hP, (perfectHomotopyObj_supported_iff z P hP).mpr hs⟩ := by
  have hz (q : ℤ) (hq : q ≠ 0) : lam.len (P.homology q) = 0 :=
    lambdaHomology_projective_vanishing lam hfg (fun j ↦ z j ^ v)
      (le_radical_span_pow z hJ v) hzero P hP hx (-(e : ℤ)) 0 hbound q (by omega)
  rw [perfectEuler_eq_length_zero lam hfg z hJ hfin P hP hs hz]
  have ht := supported_homology_isPowTorsion hfg hJ hs 0
  have hfinite := homology_mem_finiteLengthTorsion lam z hfg hJ hfin P
    (fun q ↦ (hP.2 q).1) (fun q ↦ (hP.2 q).2) ⟨-(e : ℤ), 0, hbound⟩ hs 0
  have hl := lambdaHomology_zero_minimal_lower_bound lam P
    ((hbound 1 (Or.inr one_pos)).eq_zero_of_tgt _) I hI b basis hmin ht
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_natCast] using
    ENNReal.toReal_mono hfinite.2 hl

end SerrePositivity.LengthAlgebra
