module

public import SerrePositivity.LengthAlgebra.PerfectHomologyComparison

/-! # 有限射影版の Euler 下界

Koszul 振幅を環自身の消滅から確認し、第零ホモロジーからの全射を
共通の Euler 下界へ渡す。長さの有限性は Euler 評価を定義するために使う。
-/

@[expose] public section

universe u

set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.LengthAlgebra

open CategoryTheory CategoryTheory.Limits

variable {R : Type u} [CommRing R] {J : Ideal R} (lam : NormalizedLength R J)
  (hfg : J.FG) {e : ℕ} (z : Fin e → R)
  (hJ : J ≤ (Ideal.span (Set.range z)).radical) (hfin : KoszulFinite lam z)

/-- 有限商のホモロジーの長さを、元の複体のホモロジーで計算する。 -/
lemma perfectQuotientHomology_length
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (hP : strictlyPerfectComplex R P)
    (hs : IsSupported z P) (q : ℤ) :
    quotientLength lam ((perfectQuotientHomology lam hfg z hJ hfin q).obj
      ⟨perfectHomotopyObj R P hP, (perfectHomotopyObj_supported_iff z P hP).mpr hs⟩) =
      (lam.len (P.homology q)).toReal :=
  congrArg ENNReal.toReal (lam.len_congr _ _
    (((HomotopyCategory.homologyFunctorFactors _ _ q).app P).toLinearEquiv))

lemma perfectQuotientHomology_isZero_of_len_eq_zero
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (hP : strictlyPerfectComplex R P)
    (hs : IsSupported z P) (q : ℤ) (hq : lam.len (P.homology q) = 0) :
    IsZero ((perfectQuotientHomology lam hfg z hJ hfin q).obj
      ⟨perfectHomotopyObj R P hP, (perfectHomotopyObj_supported_iff z P hP).mpr hs⟩) := by
  exact (perfectQuotientHomology_isZero_iff_lengthHomology lam hfg z hJ hfin _ q).mpr
    ((perfectLengthHomology_isZero_iff lam hfg z hJ P hP hs q).mpr hq)

/-- 具体的な Koszul 第零ホモロジーからの全射による Euler 下界。
振幅と高次 Koszul 消滅を確認した後の議論は共通定理に集約される。 -/
theorem perfectEuler_lower_bound
    (x : ℕ → R) (n : ℕ)
    (hJx : J ≤ (Ideal.span (Set.range (fun j : Fin n ↦ x j))).radical)
    (hzero : ∀ i : ℕ, 0 < i →
      lam.len (koszulHomologySelf (fun j : Fin n ↦ x j) i) = 0)
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (hP : strictlyPerfectComplex R P)
    (hs : IsSupported z P)
    (hx : ∀ j < n, Nonempty (Homotopy (smulId (x j) P) 0))
    (hbound : ∀ q, q < -(n : ℤ) ∨ 0 < q → IsZero (P.X q))
    {Y : FiniteLengthQuotient lam}
    (f : (perfectQuotientHomology lam hfg z hJ hfin 0).obj
      (perfectKoszulObj z x P hP hs n) ⟶ Y) [Epi f] :
    quotientLength lam Y ≤ perfectEuler lam hfg z hJ hfin (perfectKoszulObj z x P hP hs 0) := by
  let X := perfectKoszulObj z x P hP hs
  let T := perfectKoszulTriangle z x P hP hs
  let F := perfectQuotientHomology lam hfg z hJ hfin 0
  let f' : (F.shift (0 : ℤ)).obj (X n) ⟶ Y :=
    ((perfectQuotientHomologyShiftIso lam hfg z hJ hfin 0).app (X n)).hom ≫ f
  have : Epi f' := inferInstance
  apply iteratedZeroCone_euler_lower_bound X (fun k ↦ (T k).mor₂) (fun k ↦ (T k).mor₃)
    n (perfectKoszul_zero_triangles z x P hP hs n hx) F
    (quotientLength lam) (quotientLength_iso lam) (quotientLength_add lam)
    (quotientLength_nonneg lam) (fun Y hY ↦ (quotientLength_eq_zero_iff lam Y).mpr hY) ?_ f'
  intro q hq
  apply IsZero.of_iso _ ((perfectQuotientHomologyShiftIso lam hfg z hJ hfin q).app (X n))
  exact perfectQuotientHomology_isZero_of_len_eq_zero lam hfg z hJ hfin _ _
    (hs.koszulComplexOn _) q
    (lambdaHomology_koszul_projective_amplitude lam hfg _ hJx hzero P
      (fun q ↦ (hP.2 q).1) (fun q ↦ (hP.2 q).2) (-(n : ℤ)) 0 hbound q hq)

end SerrePositivity.LengthAlgebra
