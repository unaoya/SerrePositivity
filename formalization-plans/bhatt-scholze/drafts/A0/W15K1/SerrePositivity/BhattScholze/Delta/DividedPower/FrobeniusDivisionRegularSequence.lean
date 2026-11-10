module

public import SerrePositivity.BhattScholze.Delta.DividedPower.FrobeniusDivisionPD
public import SerrePositivity.BhattScholze.Delta.DividedPower.RegularSequencePDFactorial
public import SerrePositivity.BhattScholze.Delta.DividedPower.RegularSequencePDPrimeRegular
public import SerrePositivity.BhattScholze.Delta.Distinguished.PrimeLocalIntegers
public import SerrePositivity.BhattScholze.Andre.PowerRootEnvelope.Completion

/-!
# 正則列の Frobenius 除算

## 概要
自由 δ 座標の分冪包の計算を任意の係数に沿う押し出しで特殊化する
（BS 著者版 Lemma 2.36 と Corollary 2.39）。

## 方針
自由座標で階乗部分環と生の包の標準同型を作り、表示環と δ 除算の底変換を使う。

## 規約
通常の可換環の押し出しを使い、δ 構造は生の δ 除算から移す。

## 使われ方
結晶サイトの Frobenius で捻った分冪包。
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits SerrePositivity.DerivedCompletion
open scoped TensorProduct

universe u

namespace SerrePositivity.BhattScholze

variable {p : ℕ} [Fact p.Prime]

private theorem polynomial_primeRegular {R : Type u} [CommRing R] {σ : Type u}
    (hp : IsSMulRegular R (p : R)) :
    IsSMulRegular (MvPolynomial σ R) (p : MvPolynomial σ R) := by
  intro a b hab
  change (p : MvPolynomial σ R) * a = (p : MvPolynomial σ R) * b at hab
  apply MvPolynomial.ext
  intro m
  apply hp
  have he := congrArg (fun c : MvPolynomial σ R => c.coeff m) hab
  rw [← map_natCast (MvPolynomial.C : R →+* MvPolynomial σ R),
    MvPolynomial.coeff_C_mul, MvPolynomial.coeff_C_mul] at he
  exact he

private theorem polynomial_primeIdeal_ker {R : Type u} [CommRing R] (σ : Type u) :
    RingHom.ker (MvPolynomial.map (σ := σ) (Ideal.Quotient.mk (Ideal.span {(p : R)}))) =
      Ideal.span {(p : MvPolynomial σ R)} := by
  rw [← map_natCast (MvPolynomial.C : R →+* MvPolynomial σ R)]
  ext f
  rw [RingHom.mem_ker, Ideal.mem_span_singleton, MvPolynomial.C_dvd_iff_dvd_coeff]
  constructor
  · intro h m
    have he := congrArg (fun g : MvPolynomial σ (R ⧸ Ideal.span {(p : R)}) => g.coeff m) h
    rw [MvPolynomial.coeff_map, AddMonoidAlgebra.coeff_zero] at he
    exact Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp he)
  · intro h
    apply MvPolynomial.ext
    intro m
    rw [MvPolynomial.coeff_map, AddMonoidAlgebra.coeff_zero]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr (h m))

private def polynomialModPrimeEquiv {R : Type u} [CommRing R] (σ : Type u) :
    (MvPolynomial σ R ⧸ Ideal.span {(p : MvPolynomial σ R)}) ≃+*
      MvPolynomial σ (R ⧸ Ideal.span {(p : R)}) :=
  (Ideal.quotEquivOfEq (polynomial_primeIdeal_ker (p := p) (R := R) σ).symm).trans
    (RingHom.quotientKerEquivOfSurjective (MvPolynomial.map_surjective _
      Ideal.Quotient.mk_surjective))

section Universal

variable {R : Type u} [CommRing R] (D : DeltaStructure p R) (r : ℕ)

local notation "U" => RelativeFreeDeltaRing (R := R) (Fin r)
local notation "E" => relativeFreeDeltaStructure (Fin r) D
local notation "x" => (fun i : Fin r => (MvPolynomial.X (i, 0) : U))
local notation "b" => (fun i : Fin r => (E).frobeniusLift (x i))
local notation "C" => DeltaAdjoinDivision E (p : U) b
local notation "j" => deltaAdjoinDivisionMap E (p : U) b

private theorem freeCoordinate_primeRegular_mod (eR : (R ⧸ Ideal.span {(p : R)}) ≃+* ZMod p) :
    IsKoszulResolution (Ideal.Quotient.mk (Ideal.span {(p : U)}) ∘ x) := by
  let e := (polynomialModPrimeEquiv (p := p) (R := R) (Fin r × ℕ)).trans
    (MvPolynomial.mapEquiv (Fin r × ℕ) eR)
  have hx (i : Fin r) : e (Ideal.Quotient.mk (Ideal.span {(p : U)}) (x i)) =
      MvPolynomial.X (i,0) := by
    change (MvPolynomial.mapEquiv (Fin r × ℕ) eR)
      (MvPolynomial.map (Ideal.Quotient.mk (Ideal.span {(p : R)})) (x i)) = _
    rw [MvPolynomial.map_X, MvPolynomial.mapEquiv_apply, MvPolynomial.map_X]
  apply isKoszulResolution_of_ringEquiv e
  have h := Andre.monicRelation_fin_isKoszulResolution
    (fun _ : Fin r × ℕ => (Polynomial.X : Polynomial (ZMod p))) (fun _ => Polynomial.monic_X)
    (fun i : Fin r => (i, (0 : ℕ))) (fun _ _ h => congrArg Prod.fst h)
  simpa [hx, Andre.monicRelation] using h

/-- 概要：自由 δ 座標で生の Frobenius 除算は分冪表示と係数上で同型。
方針：両方の環を p を反転した環の階乗部分環と同定する。
規約：係数は p 局所かつ p 正則で、剰余は素数体（BS 著者版 Lemma 2.36）。
使われ方：任意の正則列への底変換と結晶側の自由模型。 -/
def freeCoordinateFrobeniusDivisionPDEquiv
    (hR : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : R)) (hpR : IsSMulRegular R (p : R))
    (eR : (R ⧸ Ideal.span {(p : R)}) ≃+* ZMod p) :
    letI : Algebra U C := (j).toAlgebra
    C ≃ₐ[U] DPFamilyPresentation x := by
  letI : Algebra U C := (j).toAlgebra
  have hlocal (m : ℕ) (hm : ¬p ∣ m) : IsUnit (m : U) := by
    simpa only [map_natCast] using (hR m hm).map (MvPolynomial.C : R →+* U)
  have hpU : IsSMulRegular U (p : U) := polynomial_primeRegular hpR
  have hpC : IsSMulRegular C (p : C) := freeCoordinateFrobeniusDivision_primeRegular D (Fin r)
    hpU ((polynomialModPrimeEquiv (Fin r × ℕ)).trans (MvPolynomial.mapEquiv _ eR))
  have hpDP := dpFamilyPresentation_primeRegular x hpU (freeCoordinate_primeRegular_mod r eR)
  have hpDP' : IsRegular (p : DPFamilyPresentation x) :=
    ⟨hpDP, fun y z h => hpDP (by simpa only [mul_comm] using h)⟩
  let l := frobeniusDivisionFactorialEquiv E x hlocal hpC
  let q := dpFamilyFactorialEquiv x hlocal hpDP'
  exact { __ := l.trans q.symm.toRingEquiv
          commutes' := fun a => by
            change q.symm (l (j a)) = algebraMap U (DPFamilyPresentation x) a
            apply q.injective
            rw [AlgEquiv.apply_symm_apply, AlgEquiv.commutes]
            exact frobeniusDivisionFactorialEquiv_base E x hlocal hpC a }

end Universal


section General

variable {A : Type u} [CommRing A] (D : DeltaStructure p A)
  (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A)) {r : ℕ} (a : Fin r → A)

local notation "Adiv" => DeltaAdjoinDivision D (p : A) (fun i => D.frobeniusLift (a i))
local notation "jA" => deltaAdjoinDivisionMap D (p : A) (fun i => D.frobeniusLift (a i))

/-- 概要：Frobenius 像を p で割る生の包は、元の族に沿う分冪表示環と同型。
方針：p 局所整数上の自由座標で比較し、指定した元への評価に沿って両方を押し出す。
規約：表示環の同型には正則性を使わない（BS 著者版 Corollary 2.39 の通常の押し出し）。
使われ方：剰余 Koszul 正則性から、生の包の p 正則性と分冪包としての普遍性を得る。 -/
def frobeniusDivisionDPFamilyEquiv :
    letI : Algebra A Adiv := (jA).toAlgebra
    Adiv ≃ₐ[A] DPFamilyPresentation a := by
  let R := PrimeLocalInt p
  let D₀ := primeLocalIntDelta p
  let U := RelativeFreeDeltaRing (R := R) (Fin r)
  let E := relativeFreeDeltaStructure (Fin r) D₀
  let x : Fin r → U := fun i => MvPolynomial.X (i, 0)
  let b : Fin r → U := fun i => E.frobeniusLift (x i)
  let C := DeltaAdjoinDivision E (p : U) b
  let j := deltaAdjoinDivisionMap E (p : U) b
  let hK := existsUnique_primeLocalIntDeltaHom p D hlocal
  let f := relativeFreeDeltaEval D hK.choose a
  have hf : E.IsDeltaHom D f :=
    relativeFreeDeltaEval_isDeltaHom D₀ D hK.choose hK.choose_spec.1 _
  have hx (i : Fin r) : f (x i) = a i := by simp [f, x]
  have hb : (fun i => f (b i)) = fun i => D.frobeniusLift (a i) := by
    funext i
    exact (hf.map_frobeniusLift (x i)).trans (congrArg D.frobeniusLift (hx i))
  have hfa : (f ∘ x) = a := funext hx
  have hpush :
      ∃ k : C →+* Adiv, IsPushout (CommRingCat.ofHom f) (CommRingCat.ofHom j)
        (CommRingCat.ofHom jA) (CommRingCat.ofHom k) := by
    have h := deltaAdjoinDivisionBaseChange_isPushout E D f hf (p : U) b
    rw [map_natCast, hb] at h
    exact ⟨_, h⟩
  obtain ⟨k, hk⟩ := hpush
  letI : Algebra U A := f.toAlgebra
  letI : Algebra U C := j.toAlgebra
  letI : Algebra A Adiv := (jA).toAlgebra
  have hpR : IsSMulRegular R (p : R) := by
    have hp₀ : (p : R) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
    intro y z hyz
    exact mul_left_cancel₀ hp₀ hyz
  let d : C ≃ₐ[U] DPFamilyPresentation x :=
    freeCoordinateFrobeniusDivisionPDEquiv D₀ r (primeLocalInt_isUnit p) hpR
      (primeLocalIntModPrimeEquiv p)
  let ht := CommRingCat.isPushout_tensorProduct U A C
  let t : A ⊗[U] C ≃+* Adiv := (ht.isoPushout ≪≫ hk.isoPushout.symm).commRingCatIsoToRingEquiv
  have htA (a₀ : A) : t (algebraMap A (A ⊗[U] C) a₀) = jA a₀ := by
    have h₁ := congr($ht.inl_isoPushout_hom a₀)
    have h₂ := congr($hk.inl_isoPushout_inv a₀)
    simpa [t, Iso.commRingCatIsoToRingEquiv, h₁] using h₂
  let t' : A ⊗[U] C ≃ₐ[A] Adiv := { __ := t, commutes' := htA }
  let w := (Algebra.TensorProduct.congr (AlgEquiv.refl : A ≃ₐ[A] A) d)
  have hd : algebraMap U A ∘ x = a := hfa
  exact t'.symm.trans (w.trans ((dpFamilyBaseChangeEquiv (B := A) x).trans
    (by rw [hd]; exact AlgEquiv.refl)))

/-- 概要：剰余上 Koszul 正則な族の生の Frobenius 除算は p 正則。
方針：正則列に沿う分冪表示環の p 正則性を標準同型で移す。
規約：BS 著者版 Corollary 2.39 の有限族。
使われ方：p 完備な結晶模型と分冪包の照合。 -/
theorem frobeniusDivision_primeRegular
    (hp : IsSMulRegular A (p : A))
    (ha : IsKoszulResolution (Ideal.Quotient.mk (Ideal.span {(p : A)}) ∘ a)) :
    IsSMulRegular Adiv (p : Adiv) := by
  let e := frobeniusDivisionDPFamilyEquiv D hlocal a
  intro x y h
  apply e.injective
  apply dpFamilyPresentation_primeRegular a hp ha
  change (p : Adiv) * x = (p : Adiv) * y at h
  simpa only [map_mul, map_natCast] using congrArg e h

/-- 概要：分冪表示に移した Frobenius 除算の δ 構造。
方針：生の δ 除算と表示環の標準同型に沿って移送する。
規約：BS 著者版 Corollary 2.39。分冪包としての解釈に剰余 Koszul 正則性を使う。
使われ方：結晶サイトの標準 δ 構造。 -/
def dpFamilyDelta : DeltaStructure p (DPFamilyPresentation a) :=
  (deltaAdjoinDivisionStructure D (p : A) (fun i => D.frobeniusLift (a i))).comapEquiv
    (frobeniusDivisionDPFamilyEquiv D hlocal a).symm.toRingEquiv

/-- 概要：移送した δ 構造は元の係数環の δ 構造を延長する。
方針：生の δ 除算の係数脚と比較同型を合成する。
規約：BS 著者版 Corollary 2.39 の δ-A 代数。
使われ方：結晶サイトでの係数写像。 -/
theorem dpFamilyDelta_algebraMap :
    D.IsDeltaHom (dpFamilyDelta D hlocal a) (algebraMap A (DPFamilyPresentation a)) := by
  let e := frobeniusDivisionDPFamilyEquiv D hlocal a
  have h := ((deltaAdjoinDivisionStructure D (p : A) (fun i => D.frobeniusLift (a i))).
    comapEquiv_symm_isDeltaHom e.symm.toRingEquiv).comp
      (deltaAdjoinDivisionMap_isDeltaHom D (p : A) (fun i => D.frobeniusLift (a i)))
  have he : e.toRingEquiv.toRingHom.comp jA = algebraMap A (DPFamilyPresentation a) := by
    apply RingHom.ext
    exact e.commutes
  exact he ▸ h

/-- 概要：Frobenius 除算と分冪表示の同型は p 完備模型に移る。
方針：標準同型は自然数 p を保つので、完備化の普遍性で延長する。
規約：BS 著者版 Corollary 2.39 の完備化への適用。
使われ方：結晶サイトの完備な自由枠。 -/
def frobeniusDivisionPDCompletionEquiv :
    letI := pdCompletionCommRing Adiv p (p : Adiv)
    letI := pdCompletionCommRing (DPFamilyPresentation a) p (p : DPFamilyPresentation a)
    PDCompletionH0 Adiv p (p : Adiv) ≃+*
      PDCompletionH0 (DPFamilyPresentation a) p (p : DPFamilyPresentation a) :=
  Andre.pdCompletionCoordinateEquiv p (frobeniusDivisionDPFamilyEquiv D hlocal a).toRingEquiv
    _ _ (map_natCast _ _)

end General

end SerrePositivity.BhattScholze
