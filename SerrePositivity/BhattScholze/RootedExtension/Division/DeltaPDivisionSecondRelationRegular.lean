module

public import SerrePositivity.BhattScholze.Delta.DividedPower.DeltaPDivisionFirstRelationRegular
public import SerrePositivity.BhattScholze.Delta.Division.DeltaDivisionFiniteResidueRelation
public import SerrePositivity.BhattScholze.RootedExtension.DeltaRoot.DeltaRootRelationKoszul
public import SerrePositivity.BhattScholze.Delta.DeltaPrime
public import Mathlib.RingTheory.Polynomial.Quotient

/-! # 最初のδ像を加えたp除算関係商のp正則性

指定した一つの関係とその最初のδ像を扱う。全δ閉包への移行は別工程。
-/

@[expose] public noncomputable section
universe u v
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}
variable (D : DeltaStructure p A) (y : σ → A) (s : σ)
local notation "L₀" => RelativeFreeDeltaRing (R := A) σ
local notation "a₀" => D.frobeniusLift (y s)
local notation "g₀" => deltaDivisionIteratedRelation D (p : A) (fun t ↦ D.frobeniusLift (y t)) s 0
local notation "g₁" => deltaDivisionIteratedRelation D (p : A) (fun t ↦ D.frobeniusLift (y t)) s 1
local notation "J₀" => Ideal.span {(p : L₀), g₀}
local notation "q₀" => Ideal.Quotient.mk J₀
local notation "I₀" => Ideal.span {(p : A), a₀}
local notation "R₀" => L₀ ⧸ Ideal.span {g₀}

/-- 最初の関係をmod pで課すイデアルは、係数側の(p,φ(y_s))の拡大。 -/
theorem deltaPDivisionFirstPairIdeal_eq_map :
    J₀ = (I₀).map (MvPolynomial.C : A →+* L₀) := by
  change Ideal.span {(p : L₀), (MvPolynomial.C (p : A) * MvPolynomial.X (s, 0) -
    MvPolynomial.C (a₀))} = _
  rw [Ideal.map_span, Set.image_insert_eq, Set.image_singleton,
    map_natCast (MvPolynomial.C : A →+* L₀) p, sub_eq_add_neg,
    Ideal.span_pair_left_mul_add, Ideal.span_pair_neg]

/-- L/(p,g_s)は係数商上の多項式環。 -/
def deltaPDivisionFirstPairPolynomialEquiv :
    (L₀ ⧸ J₀) ≃+* MvPolynomial (σ × ℕ) (A ⧸ I₀) :=
  (Ideal.quotEquivOfEq (deltaPDivisionFirstPairIdeal_eq_map D y s)).trans
    (MvPolynomial.quotientEquivQuotientMvPolynomial I₀).symm.toRingEquiv

/-- 係数商多項式表示は元の自由環の標準商像と両立する。 -/
theorem deltaPDivisionFirstPairPolynomialEquiv_mk (f : L₀) :
    deltaPDivisionFirstPairPolynomialEquiv D y s (q₀ f) =
      MvPolynomial.map (Ideal.Quotient.mk I₀) f := by
  rw [deltaPDivisionFirstPairPolynomialEquiv, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk]
  change MvPolynomial.eval₂Hom (MvPolynomial.C.comp (Ideal.Quotient.mk I₀))
    MvPolynomial.X f = MvPolynomial.map (Ideal.Quotient.mk I₀) f
  rw [← MvPolynomial.map_eq_eval₂Hom_C_comp]

/-- 最初のδ像の実mod(p,g_s)像は、単元係数1の冪関係。 -/
theorem deltaPDivisionSecondRelation_residue :
    q₀ g₁ = (q₀ (MvPolynomial.X (s, 0))) ^ p - q₀ (MvPolynomial.C (D.delta (a₀))) := by
  let F := relativeFreeDeltaStructure σ D
  have hp : q₀ (p : L₀) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
    (Ideal.subset_span (Set.mem_insert _ _))
  have hd : q₀ (MvPolynomial.C (p : A)) = 0 := by
    rw [map_natCast (MvPolynomial.C : A →+* L₀) p]
    exact hp
  have hzero : q₀ g₀ = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
    (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
  have ha : q₀ (MvPolynomial.C (a₀)) = 0 := by
    change q₀ (MvPolynomial.C (p : A) * MvPolynomial.X (s, 0) - MvPolynomial.C (a₀)) = 0 at hzero
    rw [map_sub, map_mul, hd, zero_mul, zero_sub, neg_eq_zero] at hzero
    exact hzero
  have hδp : q₀ (F.delta (MvPolynomial.C (p : A))) = 1 := by
    rw [map_natCast (MvPolynomial.C : A →+* L₀) p]
    exact F.map_delta_prime_of_zero q₀ hp
  have h := deltaDivisionFirstRelation_delta_image F q₀
    (MvPolynomial.C (p : A)) (MvPolynomial.X (s, 0)) (MvPolynomial.C (a₀)) hp hd ha
  rw [hδp, one_mul, relativeFreeDeltaStructure_delta_C] at h
  exact h

/-- 最初のδ像はL/(p,g_s)上で正則。係数環の正則性・完備性は不要。 -/
theorem deltaPDivisionSecondRelation_residue_isSMulRegular :
    IsSMulRegular (L₀ ⧸ J₀) (q₀ g₁) := by
  let e := deltaPDivisionFirstPairPolynomialEquiv D y s
  have he : e (q₀ g₁) = MvPolynomial.X (s, 0) ^ p -
      MvPolynomial.C (Ideal.Quotient.mk I₀ (D.delta (a₀))) := by
    rw [deltaPDivisionSecondRelation_residue, map_sub, map_pow,
      deltaPDivisionFirstPairPolynomialEquiv_mk, deltaPDivisionFirstPairPolynomialEquiv_mk,
      MvPolynomial.map_X, MvPolynomial.map_C]
  have hr := deltaRootRelation_isSMulRegular (p := p)
    (fun _ : σ × ℕ ↦ Ideal.Quotient.mk I₀ (D.delta (a₀))) (s, 0)
  change IsSMulRegular (MvPolynomial (σ × ℕ) (A ⧸ I₀))
    (MvPolynomial.X (s, 0) ^ p - MvPolynomial.C (Ideal.Quotient.mk I₀ (D.delta (a₀)))) at hr
  intro x z hxz
  apply e.injective
  apply hr
  have h := congrArg e hxz
  simpa only [smul_eq_mul, map_mul, he] using h

/-- 先にg_sを課した環のmod p商と、L/(p,g_s)の既存二重商比較。 -/
def deltaPDivisionFirstQuotientModPEquiv :
    (R₀ ⧸ Ideal.span {(p : R₀)}) ≃+* (L₀ ⧸ J₀) :=
  (Ideal.quotEquivOfEq (show Ideal.span {(p : R₀)} =
    (Ideal.span {(p : L₀)}).map (Ideal.Quotient.mk (Ideal.span {g₀})) from by
      rw [Ideal.map_span, Set.image_singleton,
        map_natCast (Ideal.Quotient.mk (Ideal.span {g₀})) p])).trans
    ((DoubleQuot.quotQuotEquivQuotSup (Ideal.span {g₀}) (Ideal.span {(p : L₀)})).trans
      (Ideal.quotEquivOfEq ((sup_comm _ _).trans (Ideal.span_insert (p : L₀) {g₀}).symm)))

/-- 二重商比較は自由環の標準像を保つ。 -/
theorem deltaPDivisionFirstQuotientModPEquiv_mk (f : L₀) :
    deltaPDivisionFirstQuotientModPEquiv D y s
      (Ideal.Quotient.mk _ (Ideal.Quotient.mk (Ideal.span {g₀}) f)) = q₀ f := by
  rw [deltaPDivisionFirstQuotientModPEquiv, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
    RingEquiv.trans_apply]
  change (Ideal.quotEquivOfEq _)
    (DoubleQuot.quotQuotEquivQuotSup _ _ (DoubleQuot.quotQuotMk _ _ f)) = _
  rw [DoubleQuot.quotQuotEquivQuotSup_quotQuotMk, Ideal.quotEquivOfEq_mk]

/-- g_s商のmod p上でも、最初のδ像の標準像は正則。 -/
theorem deltaPDivisionSecondRelation_firstQuotient_mod_p_isSMulRegular :
    IsSMulRegular (R₀ ⧸ Ideal.span {(p : R₀)})
      (Ideal.Quotient.mk (Ideal.span {(p : R₀)})
        (Ideal.Quotient.mk (Ideal.span {g₀}) g₁)) := by
  let e := deltaPDivisionFirstQuotientModPEquiv D y s
  intro x z hxz
  apply e.injective
  apply deltaPDivisionSecondRelation_residue_isSMulRegular D y s
  have he : e (Ideal.Quotient.mk (Ideal.span {(p : R₀)})
      (Ideal.Quotient.mk (Ideal.span {g₀}) g₁)) = q₀ g₁ :=
    deltaPDivisionFirstQuotientModPEquiv_mk D y s g₁
  have h := congrArg e hxz
  simpa only [smul_eq_mul, map_mul, he] using h

/-- 最初の関係とそのδ像の実通常商に、新しいpねじれは生じない。 -/
theorem deltaPDivisionSecondRelation_quotient_p_mul_injective
    (hpA : Function.Injective (fun x : A ↦ (p : A) * x))
    (hy : IsSMulRegular (A ⧸ Ideal.span {(p : A)})
      (Ideal.Quotient.mk (Ideal.span {(p : A)}) (y s))) :
    Function.Injective (fun x : L₀ ⧸ Ideal.span {g₀, g₁} ↦ (p : L₀ ⧸ Ideal.span {g₀, g₁}) * x) := by
  let r₁ := Ideal.Quotient.mk (Ideal.span {g₀}) g₁
  have hpR : IsSMulRegular R₀ (p : R₀) :=
    deltaPDivisionFirstRelation_quotient_p_mul_injective D y s hpA hy
  have hr := SerrePositivity.isSMulRegular_quotient_span_of_regular_mod R₀ (p : R₀) r₁ hpR
    (deltaPDivisionSecondRelation_firstQuotient_mod_p_isSMulRegular D y s)
  have hpQ : IsSMulRegular (R₀ ⧸ Ideal.span {r₁}) (p : R₀ ⧸ Ideal.span {r₁}) :=
    Eq.mp (congrArg (fun c : R₀ ⧸ Ideal.span {r₁} ↦ IsSMulRegular (R₀ ⧸ Ideal.span {r₁}) c)
      (map_natCast (Ideal.Quotient.mk (Ideal.span {r₁})) p)) hr
  let e : (R₀ ⧸ Ideal.span {r₁}) ≃+* (L₀ ⧸ Ideal.span {g₀, g₁}) :=
    (Ideal.quotEquivOfEq (show Ideal.span {r₁} =
      (Ideal.span {g₁}).map (Ideal.Quotient.mk (Ideal.span {g₀})) from by
        rw [Ideal.map_span, Set.image_singleton])).trans
      ((DoubleQuot.quotQuotEquivQuotSup (Ideal.span {g₀}) (Ideal.span {g₁})).trans
        (Ideal.quotEquivOfEq (Ideal.span_insert g₀ {g₁}).symm))
  intro x z hxz
  apply e.symm.injective
  apply hpQ
  have h := congrArg e.symm hxz
  simpa only [smul_eq_mul, map_mul, map_natCast] using h

end SerrePositivity.BhattScholze
