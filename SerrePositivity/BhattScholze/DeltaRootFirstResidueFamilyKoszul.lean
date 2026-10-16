module

public import SerrePositivity.BhattScholze.DeltaRootFiniteResidueKoszul
public import Mathlib.RingTheory.Regular.Flat

/-! # 最初の根δ関係の任意有限族の実mod(p,d)Koszul分解 -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
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

/-- 最初の実δ関係の異なる有限族は、実mod(p,d)商上で弱正則。 -/
theorem deltaRootFirstRelation_mod_pd_fin_isWeaklyRegular {m : ℕ}
    (s : Fin m → σ) (hs : Function.Injective s) :
    RingTheory.Sequence.IsWeaklyRegular (L₀ ⧸ KL₀)
      (List.ofFn fun i => Ideal.Quotient.mk KL₀
        (deltaDivisionIteratedRelation E₀ (MvPolynomial.C d) c₀ (s i) 0)) := by
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
  have hrP : RingTheory.Sequence.IsWeaklyRegular (P₀ ⧸ KP₀)
      (List.ofFn fun i => -Ideal.Quotient.mk KP₀ (c₀ (s i))) := by
    let rs := List.ofFn fun i => -Ideal.Quotient.mk KP₀ (c₀ (s i))
    refine (eP.toAddEquiv.isWeaklyRegular_congr (as := rs) (bs := rs.map eP) ?_).mpr ?_
    · apply List.forall₂_map_right_iff.mpr
      apply List.forall₂_same.mpr
      intro r _ x
      exact eP.map_mul r x
    · simpa only [rs, List.map_ofFn, Function.comp_def, map_neg, heP,
        deltaRootRelationFamily, map_sub, map_pow, MvPolynomial.map_X, MvPolynomial.map_C] using
        deltaRootRelation_neg_fin_isWeaklyRegular (p := p)
          (fun t => Ideal.Quotient.mk K₀ (b t)) s hs
  have hrL := hrP.of_flat (S := MvPolynomial (σ × ℕ) (P₀ ⧸ KP₀))
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
  have he (t : σ) : eL (Ideal.Quotient.mk KL₀
      (deltaDivisionIteratedRelation E₀ (MvPolynomial.C d) c₀ t 0)) =
      -MvPolynomial.C (Ideal.Quotient.mk KP₀ (c₀ t)) := by
    rw [heL]
    change MvPolynomial.map (Ideal.Quotient.mk KP₀)
      (MvPolynomial.C (MvPolynomial.C d) * MvPolynomial.X (t, 0) - MvPolynomial.C (c₀ t)) = _
    rw [map_sub, map_mul, MvPolynomial.map_C, MvPolynomial.map_X, MvPolynomial.map_C,
      hd, map_zero, zero_mul, zero_sub]
  let rs := List.ofFn fun i => Ideal.Quotient.mk KL₀
    (deltaDivisionIteratedRelation E₀ (MvPolynomial.C d) c₀ (s i) 0)
  refine (eL.toAddEquiv.isWeaklyRegular_congr (as := rs) (bs := rs.map eL) ?_).mpr ?_
  · apply List.forall₂_map_right_iff.mpr
    apply List.forall₂_same.mpr
    intro r _ x
    exact eL.map_mul r x
  · simpa only [rs, List.map_ofFn, Function.comp_def, he, map_neg,
      MvPolynomial.algebraMap_eq] using hrL

/-- 任意有限根族の最初の実残余Koszul複体は、対応する通常商の分解。 -/
theorem deltaRootFirstRelation_mod_pd_fin_isKoszulResolution {m : ℕ}
    (s : Fin m → σ) (hs : Function.Injective s) :
    SerrePositivity.IsKoszulResolution (fun i => Ideal.Quotient.mk KL₀
      (deltaDivisionIteratedRelation E₀ (MvPolynomial.C d) c₀ (s i) 0)) :=
  SerrePositivity.isKoszulResolution_of_isWeaklyRegular _
    (deltaRootFirstRelation_mod_pd_fin_isWeaklyRegular D d b s hs)

end SerrePositivity.BhattScholze
