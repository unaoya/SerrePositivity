module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.BhattScholze.Delta.DividedPower.Frobenius.FrobeniusDivisionPD
public import SerrePositivity.BhattScholze.Delta.DividedPower.RegularSequence.RegularSequencePDFactorial
public import SerrePositivity.BhattScholze.Delta.DividedPower.RegularSequence.RegularSequencePDPrimeRegular
public import SerrePositivity.BhattScholze.Delta.Distinguished.PrimeLocalIntegers
public import SerrePositivity.BhattScholze.Delta.Extension.PDCompletionCoordinates
import all SerrePositivity.BhattScholze.Delta.Division.Basic

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

set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.BhattScholze

variable {p : ℕ} [Fact p.Prime]

private theorem polynomial_primeRegular {R : Type u} [CommRing R] {σ : Type v}
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

private theorem polynomial_primeIdeal_ker {R : Type u} [CommRing R] (σ : Type v) :
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

private def polynomialModPrimeEquiv {R : Type u} [CommRing R] (σ : Type v) :
    (MvPolynomial σ R ⧸ Ideal.span {(p : MvPolynomial σ R)}) ≃+*
      MvPolynomial σ (R ⧸ Ideal.span {(p : R)}) :=
  (Ideal.quotEquivOfEq (polynomial_primeIdeal_ker (p := p) (R := R) σ).symm).trans
    (RingHom.quotientKerEquivOfSurjective (MvPolynomial.map_surjective _
      Ideal.Quotient.mk_surjective))

/-- 概要：有限個の δ 座標の宇宙を係数環に合わせる。
方針：有限添字を `ULift` で持ち上げる。
規約：BS 著者版 Lemma 2.36 の自由座標の添字。
使われ方：同一宇宙の可換環の押し出し。 -/
abbrev DPDivisionIndex (_ : Type u) (r : ℕ) : Type u := ULift.{u} (Fin r)

section Universal

variable {R : Type u} [CommRing R] (D : DeltaStructure p R) (r : ℕ)

local notation "Idx" => DPDivisionIndex R r
local notation "U" => RelativeFreeDeltaRing (R := R) Idx
local notation "E" => relativeFreeDeltaStructure Idx D
local notation "x" => (fun i : Fin r => (MvPolynomial.X (ULift.up i, 0) : U))
local notation "b" => (fun i : Fin r => DeltaStructure.frobeniusLift E (x i))
local notation "bUp" => (fun i : Idx => b i.down)
local notation "C" => DeltaAdjoinDivision E (p : U) bUp
local notation "j" => deltaAdjoinDivisionMap E (p : U) bUp

private theorem freeCoordinate_primeRegular_mod (eR : (R ⧸ Ideal.span {(p : R)}) ≃+* ZMod p) :
    IsKoszulResolution (Ideal.Quotient.mk (Ideal.span {(p : U)}) ∘ x) := by
  let e := (polynomialModPrimeEquiv (p := p) (R := R) (Idx × ℕ)).trans
    (MvPolynomial.mapEquiv (Idx × ℕ) eR)
  have hx (i : Fin r) : e (Ideal.Quotient.mk (Ideal.span {(p : U)}) (x i)) =
      MvPolynomial.X (ULift.up i, 0) := by
    change (MvPolynomial.mapEquiv (Idx × ℕ) eR)
      (MvPolynomial.map (Ideal.Quotient.mk (Ideal.span {(p : R)})) (x i)) = _
    rw [MvPolynomial.map_X, MvPolynomial.mapEquiv_apply, MvPolynomial.map_X]
  apply isKoszulResolution_of_ringEquiv e
  have h := Andre.monicRelation_fin_isKoszulResolution
    (fun _ : Idx × ℕ => (Polynomial.X : Polynomial (ZMod p))) (fun _ => Polynomial.monic_X)
    (fun i : Fin r => (ULift.up i, (0 : ℕ))) (fun _ _ h => congrArg (fun t => t.1.down) h)
  have heq : e.toRingHom ∘ Ideal.Quotient.mk (Ideal.span {(p : U)}) ∘ x =
      (fun i : Fin r => MvPolynomial.X (ULift.up i, 0)) := funext hx
  rw [heq]
  simpa [Andre.monicRelation] using h

/-- 概要：自由 δ 座標で生の Frobenius 除算は分冪表示と係数上で同型。
方針：両方の環を p を反転した環の階乗部分環と同定する。
規約：係数は p 局所かつ p 正則で、剰余は素数体（BS 著者版 Lemma 2.36）。
使われ方：任意の正則列への底変換と結晶側の自由模型。 -/
def freeCoordinateFrobeniusDivisionPDEquiv
    (hR : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : R)) (hpR : IsSMulRegular R (p : R))
    (eR : (R ⧸ Ideal.span {(p : R)}) ≃+* ZMod p) :
    C ≃ₐ[U] DPFamilyPresentation x := by
  have hlocal (m : ℕ) (hm : ¬p ∣ m) : IsUnit (m : U) := by
    simpa only [map_natCast] using (hR m hm).map (MvPolynomial.C : R →+* U)
  have hpU : IsSMulRegular U (p : U) := polynomial_primeRegular hpR
  have hpC : IsSMulRegular C (p : C) := freeCoordinateFrobeniusDivision_primeRegular D Idx
    hpU ((polynomialModPrimeEquiv (Idx × ℕ)).trans (MvPolynomial.mapEquiv _ eR))
  let t := deltaAdjoinDivisionReindexEquiv E (p : U) bUp b Equiv.ulift (fun _ => rfl)
  have ht (y : U) : t (j y) = deltaAdjoinDivisionMap E (p : U) b y :=
    DFunLike.congr_fun (deltaAdjoinDivisionReindexEquiv_comp E (p : U) bUp b
      Equiv.ulift (fun _ => rfl)) y
  have hpC' : IsSMulRegular (DeltaAdjoinDivision E (p : U) b) (p : DeltaAdjoinDivision E (p : U) b) := by
    intro y z h
    apply t.symm.injective
    apply hpC
    change (p : DeltaAdjoinDivision E (p : U) b) * y =
      (p : DeltaAdjoinDivision E (p : U) b) * z at h
    change (p : C) * t.symm y = (p : C) * t.symm z
    simpa only [map_mul, map_natCast] using congrArg t.symm h
  have hpDP := dpFamilyPresentation_primeRegular x hpU (freeCoordinate_primeRegular_mod r eR)
  have hpDP' : IsRegular (p : DPFamilyPresentation x) := by
    refine ⟨hpDP, ?_⟩
    intro y z hyz
    apply hpDP
    change (p : DPFamilyPresentation x) * y = (p : DPFamilyPresentation x) * z
    change y * (p : DPFamilyPresentation x) = z * (p : DPFamilyPresentation x) at hyz
    have hc (w : DPFamilyPresentation x) : (p : DPFamilyPresentation x) * w =
        w * (p : DPFamilyPresentation x) := mul_comm (p : DPFamilyPresentation x) w
    rw [hc y, hc z]
    exact hyz
  let l := frobeniusDivisionFactorialEquiv E x hlocal hpC'
  letI : Algebra U (pDivisionFactorialSubring p x) := (pDivisionFactorialBase p x).toAlgebra
  let q := dpFamilyFactorialEquiv x hlocal hpDP'
  exact { __ := t.trans (l.trans q.symm.toRingEquiv)
          commutes' := fun a => by
            change q.symm (l (t (j a))) = algebraMap U (DPFamilyPresentation x) a
            apply q.injective
            rw [AlgEquiv.apply_symm_apply, AlgEquiv.commutes, ht]
            exact frobeniusDivisionFactorialEquiv_base E x hlocal hpC' a }

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
    Adiv ≃ₐ[A] DPFamilyPresentation a := by
  let R := ULift.{u} (PrimeLocalInt p)
  let eR : R ≃+* PrimeLocalInt p := ULift.ringEquiv
  let D₀ := (primeLocalIntDelta p).comapEquiv eR
  let Idx := ULift.{u} (Fin r)
  let U := RelativeFreeDeltaRing (R := R) Idx
  let E := relativeFreeDeltaStructure Idx D₀
  let x : Fin r → U := fun i => MvPolynomial.X (ULift.up i, 0)
  let xUp : Idx → U := fun i => x i.down
  let b : Idx → U := fun i => E.frobeniusLift (xUp i)
  let C := DeltaAdjoinDivision E (p : U) b
  let j := deltaAdjoinDivisionMap E (p : U) b
  let hK := existsUnique_primeLocalIntDeltaHom p D hlocal
  let f := relativeFreeDeltaEval D (hK.choose.comp eR.toRingHom) (a ∘ ULift.down : Idx → A)
  have hf : E.IsDeltaHom D f :=
    relativeFreeDeltaEval_isDeltaHom D₀ D _ (hK.choose_spec.1.comp
      ((primeLocalIntDelta p).comapEquiv_isDeltaHom eR)) _
  have hx (i : Fin r) : f (x i) = a i := by simp [f, x]
  let c : Idx → A := fun i => D.frobeniusLift (a i.down)
  let AdivUp := DeltaAdjoinDivision D (p : A) c
  let jUp := deltaAdjoinDivisionMap D (p : A) c
  have hb : (fun i => f (b i)) = c := by
    funext i
    exact (hf.map_frobeniusLift (xUp i)).trans (congrArg D.frobeniusLift (hx i.down))
  have hfa : (f ∘ x) = a := funext hx
  let Push (d' : A) (a' : Idx → A) : Prop :=
    ∃ k : C →+* DeltaAdjoinDivision D d' a',
      IsPushout (CommRingCat.ofHom f) (CommRingCat.ofHom j)
        (CommRingCat.ofHom (deltaAdjoinDivisionMap D d' a')) (CommRingCat.ofHom k)
  have hpush : Push (p : A) c := by
    have hs : Push (f (p : U)) (fun i => f (b i)) :=
      ⟨_, deltaAdjoinDivisionBaseChange_isPushout E D f hf (p : U) b⟩
    exact (congrArg₂ Push (map_natCast f p) hb) ▸ hs
  let k := hpush.choose
  have hk : IsPushout (CommRingCat.ofHom f) (CommRingCat.ofHom j)
      (CommRingCat.ofHom jUp) (CommRingCat.ofHom k) := hpush.choose_spec
  letI : Algebra U A := f.toAlgebra
  have eR_nat (m : ℕ) : eR (m : R) = (m : PrimeLocalInt p) := rfl
  have hpR : IsSMulRegular R (p : R) := by
    have hp₀ : (p : PrimeLocalInt p) ≠ 0 := by
      intro h
      have hi := IsLocalization.injective (PrimeLocalInt p)
        (Ideal.span {(p : ℤ)}).primeCompl_le_nonZeroDivisors
      have hpZ : (p : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
      apply hpZ
      apply hi
      simpa only [map_natCast, map_zero] using h
    intro y z hyz
    apply eR.injective
    apply mul_left_cancel₀ hp₀
    change (p : R) * y = (p : R) * z at hyz
    simpa only [eR.map_mul, eR_nat] using congrArg eR hyz
  have hlocalR (m : ℕ) (hm : ¬p ∣ m) : IsUnit (m : R) := by
    let up : PrimeLocalInt p →+* R := eR.symm.toRingHom
    have hup : up (m : PrimeLocalInt p) = (m : R) := rfl
    exact hup ▸ (primeLocalInt_isUnit p m hm).map up
  let eMod : (R ⧸ Ideal.span {(p : R)}) ≃+* ZMod p :=
    (Ideal.quotientEquiv _ _ eR (by
      rw [Ideal.map_span, Set.image_singleton]
      change Ideal.span {(p : PrimeLocalInt p)} = Ideal.span {eR (p : R)}
      rw [eR_nat])).trans
      (primeLocalIntModPrimeEquiv p)
  let d : C ≃ₐ[U] DPFamilyPresentation x :=
    freeCoordinateFrobeniusDivisionPDEquiv D₀ r hlocalR hpR eMod
  let ht := CommRingCat.isPushout_tensorProduct U A C
  let t : A ⊗[U] C ≃+* AdivUp := (ht.isoIsPushout _ _ hk).commRingCatIsoToRingEquiv
  have htA (a₀ : A) : t (algebraMap A (A ⊗[U] C) a₀) = jUp a₀ := by
    exact congr($(ht.inl_isoIsPushout_hom _ _ hk).hom a₀)
  let t' : A ⊗[U] C ≃ₐ[A] AdivUp := { __ := t, commutes' := htA }
  letI : CommRing (DividedPowerAlgebra U (Fin r →₀ U)) :=
    RingCon.instCommRingQuotient (DividedPowerAlgebra.ringCon U (Fin r →₀ U))
  let w := (Algebra.TensorProduct.congr (AlgEquiv.refl : A ≃ₐ[A] A) d)
  let e := deltaAdjoinDivisionReindexEquiv D (p : A)
    (fun i : Fin r => D.frobeniusLift (a i)) c Equiv.ulift.symm (fun _ => rfl)
  have heA (y : A) : e (jA y) = jUp y :=
    DFunLike.congr_fun (deltaAdjoinDivisionReindexEquiv_comp D (p : A)
      (fun i : Fin r => D.frobeniusLift (a i)) c Equiv.ulift.symm (fun _ => rfl)) y
  let e' : Adiv ≃ₐ[A] AdivUp := { __ := e, commutes' := heA }
  have hd : algebraMap U A ∘ x = a := hfa
  exact e'.trans (t'.symm.trans (w.trans ((dpFamilyBaseChangeEquiv (B := A) x).trans
    (by rw [hd]))))

include hlocal in
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
  change (p : DPFamilyPresentation a) * e x = (p : DPFamilyPresentation a) * e y
  simpa only [map_mul, map_natCast] using congrArg e h

/-- 概要：剰余上 Koszul 正則な列の Frobenius 除算は分冪包と標準同型。
方針：生の除算を分冪表示へ移し、正則な表示を階乗部分環と同定する。
規約：BS 著者版 Corollary 2.39 の未完備な有限族。
使われ方：生の δ 除算を任意の分冪標的への普遍性と結びつける。 -/
def frobeniusDivisionDPEnvelopeEquiv (hp : IsSMulRegular A (p : A))
    (ha : IsKoszulResolution (Ideal.Quotient.mk (Ideal.span {(p : A)}) ∘ a)) :
    letI : Algebra A (pDivisionFactorialSubring p a) := (pDivisionFactorialBase p a).toAlgebra
    Adiv ≃ₐ[A] pDivisionFactorialSubring p a := by
  letI : Algebra A (pDivisionFactorialSubring p a) := (pDivisionFactorialBase p a).toAlgebra
  have h := dpFamilyPresentation_primeRegular a hp ha
  have h' : IsRegular (p : DPFamilyPresentation a) := by
    refine ⟨h, ?_⟩
    intro y z hyz
    apply h
    change (p : DPFamilyPresentation a) * y = (p : DPFamilyPresentation a) * z
    change y * (p : DPFamilyPresentation a) = z * (p : DPFamilyPresentation a) at hyz
    have hc (w : DPFamilyPresentation a) : (p : DPFamilyPresentation a) * w =
        w * (p : DPFamilyPresentation a) := mul_comm (p : DPFamilyPresentation a) w
    rw [hc y, hc z]
    exact hyz
  exact (frobeniusDivisionDPFamilyEquiv D hlocal a).trans (dpFamilyFactorialEquiv a hlocal h')

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
  let E := deltaAdjoinDivisionStructure D (p : A) (fun i => D.frobeniusLift (a i))
  have h := (E.comapEquiv_symm_isDeltaHom (A := DPFamilyPresentation a) e.symm.toRingEquiv).comp
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
      PDCompletionH0 (DPFamilyPresentation a) p (p : DPFamilyPresentation a) := by
  let e : Adiv ≃+* DPFamilyPresentation a := (frobeniusDivisionDPFamilyEquiv D hlocal a).toRingEquiv
  have he : e (p : Adiv) = (p : DPFamilyPresentation a) := map_natCast e p
  exact Andre.pdCompletionCoordinateEquiv p e _ _ he

/-- 概要：完備化の比較は元の係数環からの標準脚と可換。
方針：完備化単位との可換性と未完備比較の係数線形性を合成する。
規約：BS 著者版 Corollary 2.39 の完備化への適用。
使われ方：結晶 Čech 模型の係数脚との比較。 -/
theorem frobeniusDivisionPDCompletionEquiv_base (b : A) :
    letI := pdCompletionCommRing Adiv p (p : Adiv)
    letI := pdCompletionCommRing (DPFamilyPresentation a) p (p : DPFamilyPresentation a)
    frobeniusDivisionPDCompletionEquiv D hlocal a
        (pdCompletionUnit Adiv p (p : Adiv) (jA b)) =
      pdCompletionUnit (DPFamilyPresentation a) p (p : DPFamilyPresentation a)
        (Ideal.Quotient.mk (dpFamilyRelationIdeal a)
          (algebraMap A (DividedPowerAlgebra A (Fin r →₀ A)) b)) := by
  letI := pdCompletionCommRing Adiv p (p : Adiv)
  letI := pdCompletionCommRing (DPFamilyPresentation a) p (p : DPFamilyPresentation a)
  unfold frobeniusDivisionPDCompletionEquiv
  rw [Andre.pdCompletionCoordinateEquiv_unit]
  exact congrArg (pdCompletionUnit (DPFamilyPresentation a) p (p : DPFamilyPresentation a))
    ((frobeniusDivisionDPFamilyEquiv D hlocal a).commutes b)

end General

end SerrePositivity.BhattScholze

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite BS19 "Cor 2.39"] _root_.SerrePositivity.BhattScholze.frobeniusDivisionDPEnvelopeEquiv
attribute [cite BS19 "Cor 2.39"] _root_.SerrePositivity.BhattScholze.frobeniusDivisionDPFamilyEquiv
attribute [cite BS19 "Cor 2.39"] _root_.SerrePositivity.BhattScholze.frobeniusDivisionPDCompletionEquiv
attribute [cite BS19 "Cor 2.39"] _root_.SerrePositivity.BhattScholze.frobeniusDivision_primeRegular
attribute [cite BS19 "Lemma 2.36"] _root_.SerrePositivity.BhattScholze.freeCoordinateFrobeniusDivisionPDEquiv
