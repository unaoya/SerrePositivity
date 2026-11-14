module

public import SerrePositivity.CommutativeAlgebra.CompletelyFlat.Criterion
public import SerrePositivity.BhattScholze.Delta.Division.Basic
public import SerrePositivity.BhattScholze.Delta.Free.FreeDeltaFrobeniusFlat
import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.Algebra.Category.Ring.Colimits

/-!
# 結晶底変換での主元の正則性

## 概要
主元に関する完全平坦な代数で底変換すると、その主元の正則性が保たれる。
p 正則な δ 除算環では、p 冪ねじれを除くための標準射が同型になる。

## 方針
主元による乗法とその余核から得る短完全列に、完全平坦性による Tor 消滅を使う。

## 規約
テンソル積は通常の環のテンソル積。

## 使われ方
Frobenius に沿う結晶底変換での p ねじれの除去と mod p の計算。
-/

public noncomputable section

universe u v

open scoped TensorProduct

namespace SerrePositivity.BhattScholze.Prismatic

/-- 主元に関する完全平坦な加群とのテンソル積は、その主元の正則性を保つ。 -/
theorem crystallineTensor_isSMulRegular {R : Type u} [CommRing R] (a : R)
    (M N : Type u) [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    (hM : IsCompletelyFlat (Ideal.span {a}) M) (hN : IsSMulRegular N a) :
    IsSMulRegular (M ⊗[R] N) a := by
  let f : N →ₗ[R] N := a • LinearMap.id
  have hf : Function.Injective f := hN
  let Q := N ⧸ f.range
  have hQ : ∀ r ∈ Ideal.span {a}, ∀ x : Q, r • x = 0 := by
    intro r hr x
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton.mp hr
    induction x using Submodule.Quotient.induction_on with
    | _ x =>
      change Submodule.Quotient.mk ((a * b) • x) = (0 : Q)
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      exact ⟨b • x, (mul_smul a b x).symm⟩
  have ht : Subsingleton (TorModule R 1 M Q) :=
    (isConcentratedInDegreeZero_derivedTensor_iff M Q).mp (hM Q hQ) 1 (by decide)
  have hi := lTensor_injective_of_torModule_one M f f.range.mkQ hf f.range.mkQ_surjective
    f.exact_map_mkQ_range ht
  change Function.Injective ((a • (LinearMap.id : N →ₗ[R] N)).lTensor M) at hi
  rw [LinearMap.lTensor_smul, LinearMap.lTensor_id] at hi
  exact hi

/-- p が正則なら、Frobenius の持ち上げは δ と可換。 -/
theorem frobeniusLift_isDeltaHom_of_regular {p : ℕ} [Fact p.Prime] {R : Type u}
    [CommRing R] (D : DeltaStructure p R)
    (hp : Function.Injective (fun x : R => (p : R) * x)) :
    D.IsDeltaHom D D.frobeniusLift := by
  intro x
  apply hp
  have h (y : R) : (p : R) * D.delta y = D.frobeniusLift y - y ^ p := by
    rw [D.frobeniusLift_apply]
    ring
  calc
    (p : R) * D.frobeniusLift (D.delta x) =
        D.frobeniusLift ((p : R) * D.delta x) := by rw [map_mul, map_natCast]
    _ = D.frobeniusLift (D.frobeniusLift x) - (D.frobeniusLift x) ^ p := by
        rw [h, map_sub, map_pow]
    _ = (p : R) * D.delta (D.frobeniusLift x) := (h _).symm

private theorem deltaDivisionTorsionIdeal_eq_bot {p : ℕ} [Fact p.Prime] {R : Type u}
    [CommRing R] {σ : Type v} (D : DeltaStructure p R) (a : σ → R)
    (hp : Function.Injective (fun x : DeltaAdjoinDivision D (p : R) a => (p : _) * x)) :
    (deltaAdjoinDivisionStructure D (p : R) a).deltaClosure
      (RingHom.ker (algebraMap (DeltaAdjoinDivision D (p : R) a)
        (Localization.Away (deltaAdjoinDivisionMap D (p : R) a (p : R))))) = ⊥ := by
  let B := DeltaAdjoinDivision D (p : R) a
  let E := deltaAdjoinDivisionStructure D (p : R) a
  let d := deltaAdjoinDivisionMap D (p : R) a (p : R)
  have hd : IsLeftRegular d := by
    change Function.Injective (fun x : B => d * x)
    have h : d = (p : B) := map_natCast (deltaAdjoinDivisionMap D (p : R) a) p
    rw [h]
    exact hp
  let I := RingHom.ker (algebraMap B (Localization.Away d))
  have hI : I = ⊥ := by
    refine le_antisymm (fun x hx => ?_) bot_le
    obtain ⟨t, ht⟩ :=
      (IsLocalization.map_eq_zero_iff (Submonoid.powers d) (Localization.Away d) x).mp hx
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).mp t.property
    apply Ideal.mem_bot.mpr
    apply hd.pow n
    change d ^ n * x = d ^ n * 0
    rw [hn, ht, mul_zero]
  have hb : E.IsStable (⊥ : Ideal B) := by
    intro x hx
    simpa [Ideal.mem_bot] using congrArg E.delta (Ideal.mem_bot.mp hx)
  change E.deltaClosure I = ⊥
  rw [hI, E.deltaClosure_eq hb]

/-- p 正則な δ 除算環では、ねじれ除去は同型を与える。 -/
def deltaDivisionTorsionEquivOfPrimeRegular {p : ℕ} [Fact p.Prime] {R : Type u}
    [CommRing R] {σ : Type v} (D : DeltaStructure p R) (a : σ → R)
    (hp : Function.Injective (fun x : DeltaAdjoinDivision D (p : R) a => (p : _) * x)) :
    DeltaDivisionTorsionQuotient D (p : R) a ≃+* DeltaAdjoinDivision D (p : R) a :=
  (Ideal.quotEquivOfEq (deltaDivisionTorsionIdeal_eq_bot D a hp)).trans (RingEquiv.quotientBot _)

theorem deltaDivisionTorsionEquivOfPrimeRegular_mk {p : ℕ} [Fact p.Prime]
    {R : Type u} [CommRing R] {σ : Type v} (D : DeltaStructure p R) (a : σ → R)
    (hp : Function.Injective (fun x : DeltaAdjoinDivision D (p : R) a => (p : _) * x))
    (x : DeltaAdjoinDivision D (p : R) a) :
    deltaDivisionTorsionEquivOfPrimeRegular D a hp (Ideal.Quotient.mk _ x) = x := by
  rw [deltaDivisionTorsionEquivOfPrimeRegular, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk]
  rfl

section Completion

variable {R : Type u} [CommRing R] (a : R)

local notation "I" => (Ideal.span (Set.singleton a))
local notation "R̂" => AdicCompletion I R

private theorem adicCompletion_evalOne_ker :
    RingHom.ker (AdicCompletion.evalOneₐ I).toRingHom =
      Ideal.span {algebraMap R R̂ a} := by
  have h := AdicCompletion.ker_evalOneₐ_eq_map I (Submodule.fg_span_singleton a)
  refine h.trans (Ideal.map_span _ _ |>.trans ?_)
  exact congrArg Ideal.span (Set.image_singleton (f := algebraMap R R̂) (a := a))

/-- 主元による古典的完備化をその主元で割ると、元の環の剰余環が得られる。 -/
def crystallineAdicCompletionResidueEquiv :
    (R̂ ⧸ Ideal.span {algebraMap R R̂ a}) ≃+* R ⧸ I :=
  (Ideal.quotEquivOfEq (adicCompletion_evalOne_ker a).symm).trans
    (RingHom.quotientKerEquivOfSurjective (AdicCompletion.evalOneₐ_surjective I))

theorem crystallineAdicCompletionResidueEquiv_mk (x : R) :
    crystallineAdicCompletionResidueEquiv a (Ideal.Quotient.mk _ (algebraMap R R̂ x)) =
      Ideal.Quotient.mk I x := by
  rw [crystallineAdicCompletionResidueEquiv, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk]
  exact (AdicCompletion.evalOneₐ I).commutes x

end Completion

attribute [local instance] adicQuotientAlgebra

/-- 正則な主元と自由な剰余作用から、主元に関する完全平坦性を得る。 -/
theorem crystallineCompletelyFlat_of_freeResidue {R S B T : Type u}
    [CommRing R] [CommRing S] [CommRing B] [CommRing T] [Algebra R S]
    (a : R) (ha : IsSMulRegular R a) (hs : IsSMulRegular S a)
    (eR : (R ⧸ Ideal.span {a}) ≃+* B)
    (eS : (S ⧸ (Ideal.span {a}).map (algebraMap R S)) ≃+* T)
    (g : B →+* T)
    (hg : ∀ x : R, eS (Ideal.Quotient.mk _ (algebraMap R S x)) =
      g (eR (Ideal.Quotient.mk _ x)))
    (hFree : letI := g.toAlgebra; Module.Free B T) : IsCompletelyFlat (Ideal.span {a}) S := by
  let I : Ideal R := Ideal.span {a}
  let Q := R ⧸ I
  let J := I.map (algebraMap R S)
  let : Algebra B T := g.toAlgebra
  let : Module Q T := Module.compHom T eR.toRingHom
  let e : (S ⧸ J) ≃ₗ[Q] T := {
    eS.toAddEquiv with
    map_smul' := by
      intro r x
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      let qr : Q := Ideal.Quotient.mk I r
      let qx : S ⧸ J := Ideal.Quotient.mk J x
      change eS (qr • qx) = qr • eS qx
      have hl : qr • qx = Ideal.Quotient.mk J (algebraMap R S r) * qx := by
        rw [Algebra.smul_def]
        rfl
      have hr : qr • eS qx = g (eR qr) * eS qx := rfl
      rw [hl, hr, map_mul eS, hg]
  }
  let : Module.Free B T := hFree
  let b := (Module.Free.chooseBasis B T).mapCoeffs eR.symm (by
    intro c x
    change eR (eR.symm c) • x = c • x
    rw [eR.apply_symm_apply])
  have : Module.Free Q T := Module.Free.of_basis b
  apply isCompletelyFlat_principal_of_regular a ha S hs
  let q := (Algebra.TensorProduct.quotIdealMapEquivQuotTensor S I).toLinearEquiv
  exact Module.Flat.of_linearEquiv (q.symm.trans e)

section Frobenius

variable {R : Type u} [CommRing R] {p : ℕ} [Fact p.Prime] (D : DeltaStructure p R)

/-- Frobenius 作用を持つ終域を元の係数環と区別する型。 -/
@[expose] def CrystallineFrobeniusTarget (_D : DeltaStructure p R) := ULift.{0} R

instance crystallineFrobeniusTargetCommRing : CommRing (CrystallineFrobeniusTarget D) :=
  inferInstanceAs (CommRing (ULift.{0} R))

/-- Frobenius の持ち上げを係数射とする代数構造。 -/
abbrev crystallineFrobeniusAlgebra : Algebra R (CrystallineFrobeniusTarget D) :=
  ((ULift.ringEquiv.symm : R ≃+* CrystallineFrobeniusTarget D).toRingHom.comp D.frobeniusLift).toAlgebra

/-- 多項式剰余を持つ p 正則な δ 環の Frobenius の持ち上げは p 完全平坦。 -/
theorem crystallineCompletelyFlat_frobenius {σ : Type u}
    (hp : IsSMulRegular R (p : R))
    (eR : (R ⧸ Ideal.span {(p : R)}) ≃+* MvPolynomial σ (ZMod p)) :
    letI := crystallineFrobeniusAlgebra D
    IsCompletelyFlat (Ideal.span {(p : R)}) (CrystallineFrobeniusTarget D) := by
  let S := CrystallineFrobeniusTarget D
  let : Algebra R S := crystallineFrobeniusAlgebra D
  let I : Ideal R := Ideal.span {(p : R)}
  let J : Ideal S := Ideal.span {(p : S)}
  let e : S ≃+* R := ULift.ringEquiv
  have hJ : I.map (algebraMap R S) = J := by
    rw [show I = Ideal.span {(p : R)} from rfl, Ideal.map_span, Set.image_singleton, map_natCast]
  have hE : I = J.map e.toRingHom := by
    rw [show J = Ideal.span {(p : S)} from rfl, Ideal.map_span, Set.image_singleton,
      RingEquiv.toRingHom_eq_coe, map_natCast]
  let T := PolynomialExpandTarget p σ (ZMod p)
  let eT : MvPolynomial σ (ZMod p) ≃+* T := ULift.ringEquiv.symm
  let eS : (S ⧸ I.map (algebraMap R S)) ≃+* T :=
    (Ideal.quotEquivOfEq hJ).trans ((Ideal.quotientEquiv J I e hE).trans (eR.trans eT))
  let g : MvPolynomial σ (ZMod p) →+* T :=
    eT.toRingHom.comp (MvPolynomial.expand p).toRingHom
  have hS : IsSMulRegular S (p : R) := by
    intro x y h
    apply e.injective
    apply hp
    change (p : R) * e x = (p : R) * e y
    change (p : R) • x = (p : R) • y at h
    simp only [Algebra.smul_def, map_natCast] at h
    simpa only [map_mul, map_natCast] using congrArg e h
  apply crystallineCompletelyFlat_of_freeResidue (p : R) hp hS eR eS g
  · intro x
    have h1 : e (algebraMap R S x) = D.frobeniusLift x := rfl
    have h2 : (Ideal.Quotient.mk I) (p : R) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
    have h3 : (Ideal.Quotient.mk I) (D.frobeniusLift x) = ((Ideal.Quotient.mk I) x) ^ p := by
      rw [D.frobeniusLift_apply, map_add, map_mul, map_pow, h2, zero_mul, add_zero]
    change eS (Ideal.Quotient.mk _ (algebraMap R S x)) =
      eT (MvPolynomial.expand p (eR (Ideal.Quotient.mk I x)))
    rw [show eS (Ideal.Quotient.mk _ (algebraMap R S x)) =
      eT (eR (Ideal.Quotient.mk I (D.frobeniusLift x))) from by
        simp only [eS, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk]
        exact congrArg (fun y : R => eT (eR (Ideal.Quotient.mk I y))) h1]
    rw [h3, map_pow]
    exact congrArg eT (DFunLike.congr_fun (primePolynomial_frobenius_eq_expand p σ) _)
  · exact polynomialExpand_moduleFree p σ (ZMod p) (Fact.out : p.Prime).pos

end Frobenius

open CategoryTheory CategoryTheory.Limits in
/-- p 完全平坦な脚に沿う通常の押し出しでは、もう一方の項の p 正則性が保たれる。 -/
theorem crystallinePrimeRegular_of_isPushout {R S T U : Type u}
    [CommRing R] [CommRing S] [CommRing T] [CommRing U]
    (p : ℕ) (f : R →+* S) (g : R →+* T) (j : S →+* U) (k : T →+* U)
    (h : IsPushout (CommRingCat.ofHom f) (CommRingCat.ofHom g)
      (CommRingCat.ofHom j) (CommRingCat.ofHom k))
    (hf : letI := f.toAlgebra; IsCompletelyFlat (Ideal.span {(p : R)}) S)
    (hT : IsSMulRegular T (p : T)) : IsSMulRegular U (p : U) := by
  let : Algebra R S := f.toAlgebra
  let : Algebra R T := g.toAlgebra
  have hT' : IsSMulRegular T (p : R) := by
    intro x y hxy
    apply hT
    change (p : R) • x = (p : R) • y at hxy
    simpa only [Algebra.smul_def, map_natCast] using hxy
  have hST := crystallineTensor_isSMulRegular (p : R) S T hf hT'
  have hprod := CommRingCat.isPushout_tensorProduct R S T
  let e : S ⊗[R] T ≃+* U := (hprod.isoPushout ≪≫ h.isoPushout.symm).commRingCatIsoToRingEquiv
  intro x y hxy
  apply e.symm.injective
  apply hST
  change (p : R) • e.symm x = (p : R) • e.symm y
  change (p : U) * x = (p : U) * y at hxy
  simpa only [Algebra.smul_def, map_natCast, map_mul] using congrArg e.symm hxy

end SerrePositivity.BhattScholze.Prismatic
