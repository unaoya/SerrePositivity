module

public import SerrePositivity.CommutativeAlgebra.ReesCoefficientApproximation
public import SerrePositivity.CommutativeAlgebra.AdicCompletionQuotient
public import Mathlib.RingTheory.AdicCompletion.LocalRing

/-! # 商のNoether性から完備環のNoether性へ

有限生成イデアルの随伴次数環で初期形式を有限個選び、
係数の次数を制御した近似を完備性で持ち上げる。係数sectionは要求しない。
-/

public section
universe u
namespace SerrePositivity
variable (R : Type u) [CommRing R] (I : Ideal R)

/-- 完備環の各イデアルは、商がNoetherで定義イデアルが有限生成なら有限生成。 -/
theorem ideal_fg_of_adicComplete_of_noetherian_quotient
    [IsAdicComplete I R] [IsNoetherianRing (R ⧸ I)] (hI : I.FG) (J : Ideal R) : J.FG := by
  obtain ⟨r, z, hz, hspan⟩ := HilbertSamuel.exists_finite_reesCoefficientIdeal_lifts R I J hI
  obtain ⟨c, f, hf, happrox⟩ :=
    HilbertSamuel.exists_shifted_approximation_of_rees_lifts I J z hz hspan
  apply fg_of_shifted_adic_approximation I f J hf c
  intro n x hxJ hxI
  obtain ⟨v, hv, herr⟩ := happrox n x hxJ (by simpa only [smul_eq_mul, Ideal.mul_top] using hxI)
  exact ⟨v, hv, by simpa only [smul_eq_mul, Ideal.mul_top] using herr⟩

/-- 有限生成イデアルに沿う完備環は、その商がNoetherならNoether。
元の環のNoether性や商からの係数sectionを仮定しない。 -/
theorem isNoetherianRing_of_adicComplete_of_noetherian_quotient
    [IsAdicComplete I R] [IsNoetherianRing (R ⧸ I)] (hI : I.FG) : IsNoetherianRing R := by
  apply (isNoetherianRing_iff_ideal_fg R).mpr
  exact ideal_fg_of_adicComplete_of_noetherian_quotient R I hI

/-- 有限生成な極大イデアルに関して完備な局所環はNoether。 -/
theorem isNoetherianRing_of_complete_local_of_fg [IsLocalRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    (h : (IsLocalRing.maximalIdeal R).FG) : IsNoetherianRing R := by
  let : IsNoetherianRing (R ⧸ IsLocalRing.maximalIdeal R) :=
    inferInstanceAs (IsNoetherianRing (IsLocalRing.ResidueField R))
  exact isNoetherianRing_of_adicComplete_of_noetherian_quotient R _ h

/-- 元の環が非Noetherでも、有限生成イデアルによる商がNoetherなら完備化はNoether。 -/
theorem isNoetherianRing_adicCompletion_of_noetherian_quotient
    [IsNoetherianRing (R ⧸ I)] (hI : I.FG) : IsNoetherianRing (AdicCompletion I R) := by
  let C := AdicCompletion I R
  let J := I.map (algebraMap R C)
  let : IsAdicComplete J C := AdicCompletion.isAdicComplete_self I hI
  let e : (C ⧸ J) ≃ₐ[R] (R ⧸ I) :=
    ((Ideal.quotientEquivAlgOfEq R (pow_one J).symm).trans
      (adicCompletionPowQuotientEquiv I hI 1)).trans
      (Ideal.quotientEquivAlgOfEq R (pow_one I))
  let : IsNoetherianRing (C ⧸ J) := isNoetherianRing_of_ringEquiv (R ⧸ I) e.symm.toRingEquiv
  exact isNoetherianRing_of_adicComplete_of_noetherian_quotient C J (hI.map _)

end SerrePositivity
