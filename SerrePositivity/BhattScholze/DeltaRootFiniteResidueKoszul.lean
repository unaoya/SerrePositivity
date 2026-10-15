module

public import SerrePositivity.BhattScholze.DeltaDivisionFiniteResidueKoszul
public import SerrePositivity.BhattScholze.DeltaRootFirstEvaluationKoszul

/-! # 一元根添加の全有限δ深さのmod(p,d)Koszul分解

初項の正則性はモニック根関係から供給する。高段のp正則性・ghost単射・指定単元は明示する。
通常mod(p,d)商上の分解であり、導来完備化後の完全忠実平坦性とは区別する。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (d : A) (b : σ → A)
local notation "P₀" => MvPolynomial σ A
local notation "L₀" => RelativeFreeDeltaRing (R := P₀) σ
local notation "E₀" => polynomialRankOneDeltaStructure σ D
local notation "c₀" => deltaRootRelationFamily (p := p) b
local notation "K₀" => Ideal.span {(p : A), d}
local notation "KP₀" => Ideal.span {(p : P₀), MvPolynomial.C d}
local notation "KL₀" => Ideal.span {(p : L₀), MvPolynomial.C (MvPolynomial.C d)}

/-- 任意dの最初の根除算関係は、実mod(p,d)商上の非零因子。 -/
theorem deltaRootFirstRelation_mod_pd_isSMulRegular (s : σ) :
    IsSMulRegular (L₀ ⧸ KL₀)
      (Ideal.Quotient.mk KL₀ (deltaDivisionIteratedRelation E₀ (MvPolynomial.C d) c₀ s 0)) := by
  have hP : (K₀).map (MvPolynomial.C : A →+* P₀) = KP₀ := by
    rw [Ideal.map_span]
    simp only [Set.image_pair, map_natCast]
  let eP := (Ideal.quotEquivOfEq hP.symm).trans
    (MvPolynomial.quotientEquivQuotientMvPolynomial (σ := σ) K₀).symm.toRingEquiv
  have heP (f : P₀) : eP (Ideal.Quotient.mk KP₀ f) =
      MvPolynomial.map (Ideal.Quotient.mk K₀) f := by
    dsimp only [eP]
    rw [RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk]
    exact RingHom.congr_fun (monicPowerFamilyCoefficientQuotient_comp σ A K₀) f
  have hr := deltaRootRelation_map_isSMulRegular (p := p) (Ideal.Quotient.mk K₀) b s
  have hrP : IsSMulRegular (P₀ ⧸ KP₀) (Ideal.Quotient.mk KP₀ (c₀ s)) := by
    intro x y hxy
    apply eP.injective
    apply hr
    have h := congrArg eP hxy
    simpa only [smul_eq_mul, map_mul, heP] using h
  have hrL := hrP.of_flat (S := MvPolynomial (σ × ℕ) (P₀ ⧸ KP₀))
  change IsSMulRegular (MvPolynomial (σ × ℕ) (P₀ ⧸ KP₀))
    (MvPolynomial.C (σ := σ × ℕ) (Ideal.Quotient.mk KP₀ (c₀ s))) at hrL
  have hL : (KP₀).map (MvPolynomial.C : P₀ →+* L₀) = KL₀ := by
    rw [Ideal.map_span]
    simp only [Set.image_pair, map_natCast]
  let eL := (Ideal.quotEquivOfEq hL.symm).trans
    (MvPolynomial.quotientEquivQuotientMvPolynomial (σ := σ × ℕ) KP₀).symm.toRingEquiv
  have heL (f : L₀) : eL (Ideal.Quotient.mk KL₀ f) =
      MvPolynomial.map (Ideal.Quotient.mk KP₀) f := by
    dsimp only [eL]
    rw [RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk]
    exact RingHom.congr_fun (monicPowerFamilyCoefficientQuotient_comp (σ × ℕ) P₀ KP₀) f
  have hd : Ideal.Quotient.mk KP₀ (MvPolynomial.C d) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
  have he : eL (Ideal.Quotient.mk KL₀
      (deltaDivisionIteratedRelation E₀ (MvPolynomial.C d) c₀ s 0)) =
      -MvPolynomial.C (Ideal.Quotient.mk KP₀ (c₀ s)) := by
    rw [heL]
    change MvPolynomial.map (Ideal.Quotient.mk KP₀)
      (MvPolynomial.C (MvPolynomial.C d) * MvPolynomial.X (s, 0) - MvPolynomial.C (c₀ s)) = _
    rw [map_sub, map_mul, MvPolynomial.map_C, MvPolynomial.map_X, MvPolynomial.map_C,
      hd, map_zero, zero_mul, zero_sub]
  intro x y hxy
  apply eL.injective
  apply hrL
  have h := congrArg eL hxy
  simpa only [smul_eq_mul, map_mul, he, neg_mul, neg_inj] using h

/-- 一元根添加の全有限δ列は、明示した正規化入力の下で実mod(p,d)Koszul分解を与える。 -/
theorem deltaRootFiniteResidueRelations_isKoszulResolution [Unique σ]
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (hg : Function.Injective (WittVector.ghostMap : WittVector p L₀ → ℕ → L₀))
    (v : Aˣ) (hv : (v : A) = D.delta d) (N : ℕ) :
    SerrePositivity.IsKoszulResolution (fun i : Fin (N + 1) =>
      Ideal.Quotient.mk KL₀
        (deltaDivisionIteratedRelation E₀ (MvPolynomial.C d) c₀ default i.val)) := by
  have hpP : IsSMulRegular P₀ (p : P₀) := by
    simpa only [map_natCast] using (show IsSMulRegular A (p : A) from hpA).of_flat (S := P₀)
  have hpL : IsSMulRegular L₀ (p : L₀) := by
    simpa only [map_natCast] using hpP.of_flat (S := L₀)
  let vP := v.map (MvPolynomial.C : A →+* P₀).toMonoidHom
  have hvP : (vP : P₀) = (E₀).delta (MvPolynomial.C d) := by
    change MvPolynomial.C (v : A) = _
    rw [hv, polynomialRankOneDeltaStructure_delta_C]
  exact deltaDivisionFiniteResidueRelations_isKoszulResolution E₀ (MvPolynomial.C d) c₀
    hpP hpL hg vP hvP (deltaRootFirstRelation_mod_pd_isSMulRegular D d b default) N

end SerrePositivity.BhattScholze
