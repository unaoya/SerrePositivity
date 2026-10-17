module

public import SerrePositivity.BhattScholze.Andre.MonicRelationRegularSequence
public import SerrePositivity.BhattScholze.DeltaRootFiniteResidueKoszul
public import Mathlib.RingTheory.Regular.Flat

/-!
# André E1・E2：モニック族の最初の実 δ 剰余関係の Koszul 分解

## 概要

任意モニック族の f/d 包の最初の δ 関係は、実 (p,d) 商で弱正則列をなす。
BS Rem 7.15（著者版 p.62）の実導来剰余の離散性への入力。

## 方針

二重多項式係数商を展開し、d の像が零となることで各関係を負のモニック関係に移す。
原典の Prop 7.11 を使う証明とは異なる経路の計算。

## 規約

有限個の異なる添字を選ぶが、全添字型の有限性は要求しない。正次数も不要。

## 使われ方

一般 δ 除算の有限深さの既存弱正則性定理へ渡す。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (d : A) (f : σ → Polynomial A)
local notation "P₀" => MvPolynomial σ A
local notation "L₀" => RelativeFreeDeltaRing (R := P₀) σ
local notation "E₀" => polynomialRankOneDeltaStructure σ D
local notation "c₀" => (fun s : σ => monicRelation (f s) s)
local notation "K₀" => Ideal.span {(p : A), d}
local notation "KP₀" => Ideal.span {(p : P₀), MvPolynomial.C d}
local notation "KL₀" => Ideal.span {(p : L₀), MvPolynomial.C (MvPolynomial.C d)}

/-- 概要：最初の実δ関係の異なる有限族は、実mod(p,d)商上で弱正則。
方針：二重係数商の表示で最初の関係を負のモニック関係族に移す。
規約：係数環の p 正則性や多項式の正次数は不要。
使われ方：BS Rem 7.15（著者版 p.62）の全有限 δ 深さへの初項入力。 -/
theorem monicPrismaticFirstRelation_mod_pd_fin_isWeaklyRegular
    (hf : ∀ s, (f s).Monic) {m : ℕ}
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
    · simpa only [rs, List.map_ofFn, Function.comp_def, map_neg, heP, monicRelation_map] using
        monicRelation_neg_fin_isWeaklyRegular
          (fun t => (f t).map (Ideal.Quotient.mk K₀))
          (fun t => (hf t).map (Ideal.Quotient.mk K₀)) s hs
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

/-- 概要：任意有限モニック族の最初の実残余Koszul複体は、対応する通常商の分解。
方針：二重係数商の表示で最初の関係を負のモニック関係族に移す。
規約：係数環の p 正則性や多項式の正次数は不要。
使われ方：BS Rem 7.15（著者版 p.62）の全有限 δ 深さへの初項入力。 -/
theorem monicPrismaticFirstRelation_mod_pd_fin_isKoszulResolution
    (hf : ∀ s, (f s).Monic) {m : ℕ}
    (s : Fin m → σ) (hs : Function.Injective s) :
    SerrePositivity.IsKoszulResolution (fun i => Ideal.Quotient.mk KL₀
      (deltaDivisionIteratedRelation E₀ (MvPolynomial.C d) c₀ (s i) 0)) :=
  SerrePositivity.isKoszulResolution_of_isWeaklyRegular _
    (monicPrismaticFirstRelation_mod_pd_fin_isWeaklyRegular D d f hf s hs)

end SerrePositivity.BhattScholze.Andre
