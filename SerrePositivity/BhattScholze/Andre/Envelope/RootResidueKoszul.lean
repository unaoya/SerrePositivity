module

public import SerrePositivity.BhattScholze.Andre.Envelope.SourceEvaluation
public import SerrePositivity.BhattScholze.Andre.Envelope.RootRelation
public import SerrePositivity.BhattScholze.Andre.Envelope.JetKoszul
public import Mathlib.RingTheory.Regular.Flat
public import SerrePositivity.BhattScholze.Andre.Envelope.JetRegularity
public import SerrePositivity.BhattScholze.Andre.Envelope.RootFamilyRaw
public import SerrePositivity.BhattScholze.Andre.Envelope.PDivision

/-!
# 根添加の剰余の Koszul 分解

## 概要
一般の d 根添加の最初の有限評価関係、一元根添加の全有限 δ 深さの mod (p,d) Koszul 分解と源 Tor、最初の根 δ 関係の有限族の Koszul 分解、有限添字・二つの独立根関係の raw p 除算包の p 正則性。
BS 著者版 Proposition 3.13 と Remark 7.15 の包の計算に使う、根関係の剰余の Koszul 分解を与える。

## 方針
構成ごとに補題をまとめ、各節で共通の仮定を明示する。

## 規約
係数環・素数・正則性の仮定は各宣言で明示する。

## 使われ方
`Envelope/FamilyEvaluation`、`Envelope/MonicCandidate`、`Envelope/RootSource`。
-/

universe u v

/-! ## 一般d根添加の最初の有限評価関係のKoszul分解

根変数と自由δ変数を交換すると、深さ0の関係はモニック根関係の負になる。
正のδ深さ・全源評価環への移行・完備化後の平坦性は含まない。
-/

@[expose] public noncomputable section DeltaRootFirstEvaluationKoszul

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze

private theorem neg_list_regular {R : Type u} [CommRing R] (l : List R)
    (h : RingTheory.Sequence.IsWeaklyRegular R l) :
    RingTheory.Sequence.IsWeaklyRegular R (l.map fun x => -x) := by
  have hI (t : List R) : Ideal.ofList (t.map fun x => -x) = Ideal.ofList t := by
    induction t with
    | nil => rfl
    | cons x t ih => simp only [List.map_cons, Ideal.ofList_cons, ih, Ideal.span_singleton_neg]
  constructor
  intro i hi
  have hi' : i < l.length := by simpa only [List.length_map] using hi
  have hr := h.regular_mod_prev i hi'
  rw [← List.map_take, hI, List.getElem_map]
  intro x y hxy
  apply hr
  exact neg_injective (by simpa only [neg_smul] using hxy)

variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
/-- 負のモニック根関係の異なる有限族も、任意係数環上で弱正則。 -/
theorem deltaRootRelation_neg_fin_isWeaklyRegular (b : σ → A) {m : ℕ}
    (s : Fin m → σ) (hs : Function.Injective s) :
    RingTheory.Sequence.IsWeaklyRegular (MvPolynomial σ A)
      (List.ofFn fun i => -deltaRootRelationFamily (p := p) b (s i)) := by
  simpa only [List.map_ofFn, Function.comp_def] using
    neg_list_regular _ (deltaRootRelation_fin_isWeaklyRegular (p := p) b s hs)

variable (D : DeltaStructure p A) (d : A) (b : σ → A)
local notation "P₀" => MvPolynomial σ A
local notation "E₀" => polynomialRankOneDeltaStructure σ D
local notation "c₀" => deltaRootRelationFamily (p := p) b

/-- 変数交換で最初の実評価関係は、移動した係数上のモニック根関係の負になる。 -/
theorem deltaRootFirstEvaluation_swap (s : σ) :
    MvPolynomial.commAlgEquiv A (σ × ℕ) σ
      (deltaDivisionEvaluationRelation E₀ (MvPolynomial.C d) c₀ s 0) =
      -(deltaRootRelationFamily (p := p)
        (fun t : σ => MvPolynomial.C d * MvPolynomial.X (t, 0) + MvPolynomial.C (b t)) s) := by
  simp only [deltaDivisionEvaluationRelation, Function.iterate_zero_apply,
    deltaRootRelationFamily, map_sub, map_mul, MvPolynomial.commAlgEquiv_C,
    MvPolynomial.commAlgEquiv_X, MvPolynomial.map_C, map_pow, MvPolynomial.map_X,
    MvPolynomial.C_add]
  ring

/-- 任意dに対し、異なる有限個の根の深さ0評価関係は弱正則列。 -/
theorem deltaRootFirstEvaluation_fin_isWeaklyRegular {m : ℕ}
    (s : Fin m → σ) (hs : Function.Injective s) :
    RingTheory.Sequence.IsWeaklyRegular (RelativeFreeDeltaRing (R := P₀) σ)
      (List.ofFn fun i => deltaDivisionEvaluationRelation E₀ (MvPolynomial.C d) c₀ (s i) 0) := by
  let e := MvPolynomial.commAlgEquiv A (σ × ℕ) σ
  let c : σ → MvPolynomial (σ × ℕ) A :=
    fun t => MvPolynomial.C d * MvPolynomial.X (t, 0) + MvPolynomial.C (b t)
  have hr := neg_list_regular _ (deltaRootRelation_fin_isWeaklyRegular (p := p) c s hs)
  have hc := e.toRingEquiv.toAddEquiv.isWeaklyRegular_congr
    (as := List.ofFn fun i => deltaDivisionEvaluationRelation E₀ (MvPolynomial.C d) c₀ (s i) 0)
    (bs := (List.ofFn fun i =>
      deltaDivisionEvaluationRelation E₀ (MvPolynomial.C d) c₀ (s i) 0).map e)
    (List.forall₂_map_right_iff.mpr (List.forall₂_same.mpr
      (fun r _ x => by
        change e (r * x) = e r * e x
        exact map_mul e r x)))
  apply hc.mpr
  simpa only [List.map_ofFn, Function.comp_def, e, deltaRootFirstEvaluation_swap] using hr

/-- 根添加の最初の有限評価Koszul複体は、実通常商の分解。 -/
theorem deltaRootFirstEvaluation_fin_isKoszulResolution {m : ℕ}
    (s : Fin m → σ) (hs : Function.Injective s) :
    SerrePositivity.IsKoszulResolution
      (fun i => deltaDivisionEvaluationRelation E₀ (MvPolynomial.C d) c₀ (s i) 0) :=
  SerrePositivity.isKoszulResolution_of_isWeaklyRegular _
    (deltaRootFirstEvaluation_fin_isWeaklyRegular D d b s hs)

/-- 一般dの実自由δ射に沿う深さ0有限源グラフ商の正次数Torは零。 -/
theorem deltaRootFirstEvaluation_source_tor_subsingleton {m : ℕ}
    (s : Fin m → σ) (hs : Function.Injective s) (i : ℕ) :
    Subsingleton (SerrePositivity.TorAlg
      (deltaDivisionSourceMap (σ := σ) E₀ (MvPolynomial.C d)) (i + 1)
      (DeltaDivisionSourceFiniteCoordinateQuotient E₀ c₀ (fun j => (s j, 0)))) := by
  apply deltaDivisionSourceFiniteCoordinate_tor_subsingleton
  · intro j k h
    exact hs (congrArg Prod.fst h)
  · exact deltaRootFirstEvaluation_fin_isKoszulResolution D d b s hs

end SerrePositivity.BhattScholze

end DeltaRootFirstEvaluationKoszul

/-! ## 一元根添加の全有限δ深さのmod(p,d)Koszul分解

初項の正則性はモニック根関係から供給する。高段のp正則性・ghost単射・指定単元は明示する。
通常mod(p,d)商上の分解であり、導来完備化後の完全忠実平坦性とは区別する。
-/

@[expose] public noncomputable section DeltaRootFiniteResidueKoszul

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

/-- 一元根添加の全有限δ列は、明示した正規化入力の下で実mod(p,d)弱正則列となる。 -/
theorem deltaRootFiniteResidueRelations_isWeaklyRegular [Unique σ]
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (hg : Function.Injective (WittVector.ghostMap : WittVector p L₀ → ℕ → L₀))
    (v : Aˣ) (hv : (v : A) = D.delta d) (N : ℕ) :
    RingTheory.Sequence.IsWeaklyRegular (L₀ ⧸ KL₀)
      (List.ofFn fun i : Fin (N + 1) =>
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
  exact deltaDivisionFiniteResidueRelations_isWeaklyRegular E₀ (MvPolynomial.C d) c₀
    hpP hpL hg vP hvP (deltaRootFirstRelation_mod_pd_isSMulRegular D d b default) N


/-- 一元根添加の全有限δ列は、明示した正規化入力の下で実mod(p,d)Koszul分解を与える。 -/
theorem deltaRootFiniteResidueRelations_isKoszulResolution [Unique σ]
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (hg : Function.Injective (WittVector.ghostMap : WittVector p L₀ → ℕ → L₀))
    (v : Aˣ) (hv : (v : A) = D.delta d) (N : ℕ) :
    SerrePositivity.IsKoszulResolution (fun i : Fin (N + 1) =>
      Ideal.Quotient.mk KL₀
        (deltaDivisionIteratedRelation E₀ (MvPolynomial.C d) c₀ default i.val)) :=
  SerrePositivity.isKoszulResolution_of_isWeaklyRegular _
    (deltaRootFiniteResidueRelations_isWeaklyRegular D d b hpA hg v hv N)

end SerrePositivity.BhattScholze

end DeltaRootFiniteResidueKoszul

/-! ## 最初の根δ関係の任意有限族の実mod(p,d)Koszul分解 -/

@[expose] public noncomputable section DeltaRootFirstResidueFamilyKoszul

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

end DeltaRootFirstResidueFamilyKoszul

/-! ## 一元根添加の全有限深さの実残余評価Koszul分解と源Tor

実自由δ射αの後にmod(p,d)商射を合成した通常射を使う。
全源評価環のTorや実導来完備化後の完全忠実平坦性はここでは結論しない。
-/

@[expose] public noncomputable section DeltaRootFiniteResidueSourceTor

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open CategoryTheory
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A] [Unique σ]
variable (D : DeltaStructure p A) (d : A) (b : σ → A)
local notation "P₀" => MvPolynomial σ A
local notation "L₀" => RelativeFreeDeltaRing (R := P₀) σ
local notation "E₀" => polynomialRankOneDeltaStructure σ D
local notation "c₀" => deltaRootRelationFamily (p := p) b
local notation "K₀" => Ideal.span {(p : L₀), MvPolynomial.C (MvPolynomial.C d)}
local notation "q₀" => Ideal.Quotient.mk K₀
local notation "α₀" => deltaDivisionSourceMap (σ := σ) E₀ (MvPolynomial.C d)

/-- 一元根添加の全有限深さの実評価列は、実mod(p,d)商上でKoszul分解を与える。 -/
theorem deltaRootFiniteResidueEvaluation_isKoszulResolution
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (hg : Function.Injective (WittVector.ghostMap : WittVector p L₀ → ℕ → L₀))
    (v : Aˣ) (hv : (v : A) = D.delta d) (N : ℕ) :
    SerrePositivity.IsKoszulResolution (fun i : Fin (N + 1) =>
      q₀ (deltaDivisionEvaluationRelation E₀ (MvPolynomial.C d) c₀ default i.val)) :=
  deltaDivisionMappedEvaluation_isKoszulResolution E₀ (MvPolynomial.C d) c₀ q₀
    (deltaRootFiniteResidueRelations_isWeaklyRegular D d b hpA hg v hv) N

/-- 実残余自由δ射に沿う全有限源グラフ商のTorを、実残余評価Koszulホモロジーで計算する。 -/
def deltaRootFiniteResidueSourceKoszulTorIso (N i : ℕ) :
    ((ModuleCat.extendScalars.{u, u, u} ((q₀).comp α₀)).leftDerived i).obj
      (ModuleCat.of L₀ (DeltaDivisionSourceFiniteCoordinateQuotient E₀ c₀
        (fun j : Fin (N + 1) => (default, j.val)))) ≅
      (SerrePositivity.koszulComplex (fun j : Fin (N + 1) =>
        q₀ (deltaDivisionEvaluationRelation E₀ (MvPolynomial.C d) c₀ default j.val))).homology
          (-(i : ℤ)) := by
  have e := SerrePositivity.torAlgKoszulIso ((q₀).comp α₀)
    (fun j : Fin (N + 1) => deltaDivisionSourceGraphRelation E₀ c₀ (default, j.val))
    (deltaDivisionSourceGraph_fin_isKoszulResolution E₀ c₀
      (fun j : Fin (N + 1) => (default, j.val))
      (fun _ _ hij => Fin.ext (congrArg Prod.snd hij))) i
  have he : ((q₀).comp α₀) ∘
      (fun j : Fin (N + 1) => deltaDivisionSourceGraphRelation E₀ c₀ (default, j.val)) =
      (fun j : Fin (N + 1) =>
        q₀ (deltaDivisionEvaluationRelation E₀ (MvPolynomial.C d) c₀ default j.val)) := by
    funext j
    exact congrArg q₀ (deltaDivisionSourceGraph_map E₀ (MvPolynomial.C d) c₀ (default, j.val))
  rw [he] at e
  exact e

/-- 明示した正規化入力の下、実残余自由δ射に沿う任意有限源商の全正次数Torは零。 -/
theorem deltaRootFiniteResidueSource_tor_subsingleton
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (hg : Function.Injective (WittVector.ghostMap : WittVector p L₀ → ℕ → L₀))
    (v : Aˣ) (hv : (v : A) = D.delta d) (N i : ℕ) :
    Subsingleton (SerrePositivity.TorAlg ((q₀).comp α₀) (i + 1)
      (DeltaDivisionSourceFiniteCoordinateQuotient E₀ c₀
        (fun j : Fin (N + 1) => (default, j.val)))) := by
  have hr := deltaRootFiniteResidueEvaluation_isKoszulResolution D d b hpA hg v hv N
  have hz := hr.isZero (-((i + 1 : ℕ) : ℤ)) (by omega)
  have ht := hz.of_iso (deltaRootFiniteResidueSourceKoszulTorIso D d b N (i + 1))
  exact ModuleCat.subsingleton_of_isZero ht

end SerrePositivity.BhattScholze

end DeltaRootFiniteResidueSourceTor

/-! ## 有限添字の全根関係族のraw p除算包のp正則性 -/

@[expose] public noncomputable section DeltaRootFiniteFamilyRegular

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v} [Finite σ]
variable {η : Type (max u v)} [Unique η]
variable (D : DeltaStructure p A) (b : σ → A)
local notation "P" => MvPolynomial σ A
local notation "E" => polynomialRankOneDeltaStructure σ D
local notation "r" => deltaRootRelationFamily (p := p) b

/-- 有限添字の全族raw包は、有限部分集合版の証明からp正則となる。
ghost入力は先行raw包のp正則性を受け取る形で保持し、循環依存を作らない。 -/
theorem deltaRootFiniteFamilyRaw_p_mul_injective
    (hpA : Function.Injective (fun z : A ↦ (p : A) * z))
    (w : Aˣ) (hw : (w : A) = D.delta (p : A))
    (hg₀ : ∀ T : Finset σ, Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := P) T) → ℕ → RelativeFreeDeltaRing (R := P) T))
    (hg₁ : ∀ T : Finset σ,
      Function.Injective (fun z : DeltaAdjoinDivision E (p : P)
        (fun t : T ↦ DeltaStructure.frobeniusLift E (r t)) ↦
        (p : DeltaAdjoinDivision E (p : P)
          (fun t : T ↦ DeltaStructure.frobeniusLift E (r t))) * z) →
      Function.Injective (WittVector.ghostMap :
        WittVector p (RelativeFreeDeltaRing
          (R := DeltaAdjoinDivision E (p : P)
            (fun t : T ↦ DeltaStructure.frobeniusLift E (r t))) η) →
        ℕ → RelativeFreeDeltaRing
          (R := DeltaAdjoinDivision E (p : P)
            (fun t : T ↦ DeltaStructure.frobeniusLift E (r t))) η)) :
    Function.Injective (fun z : DeltaAdjoinDivision E (p : P)
      (fun t : σ ↦ DeltaStructure.frobeniusLift E (r t)) ↦
      (p : DeltaAdjoinDivision E (p : P)
        (fun t : σ ↦ DeltaStructure.frobeniusLift E (r t))) * z) := by
  classical
  let := Fintype.ofFinite σ
  let T : Finset σ := Finset.univ
  have hpT := deltaRootFiniteRaw_p_mul_injective (η := η) D b hpA w hw hg₀ hg₁ T
  let e : (T : Type v) ≃ σ :=
    { toFun := Subtype.val
      invFun := fun s ↦ ⟨s, by simp [T]⟩
      left_inv := fun s ↦ Subtype.ext rfl
      right_inv := fun _ ↦ rfl }
  let eB := deltaAdjoinDivisionReindexEquiv E (p : P)
    (fun t : T ↦ DeltaStructure.frobeniusLift E (r t))
    (fun t : σ ↦ DeltaStructure.frobeniusLift E (r t)) e (fun _ ↦ rfl)
  intro z t hzt
  apply eB.symm.injective
  apply hpT
  simpa only [map_mul, map_natCast] using congrArg eB.symm hzt

end SerrePositivity.BhattScholze

end DeltaRootFiniteFamilyRegular

/-! ## 二つの独立根関係の具体的raw p除算包のp正則性 -/

@[expose] public noncomputable section DeltaRootPairRawRegular

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} {σ : Type v} {η : Type (max u v)}
  [CommRing A] [Unique η]
variable (D : DeltaStructure p A) (b : σ → A) (s t : σ)
local notation "P" => MvPolynomial σ A
local notation "E" => polynomialRankOneDeltaStructure σ D
local notation "rs" => deltaRootRelationFamily (p := p) b s
local notation "rt" => deltaRootRelationFamily (p := p) b t
local notation "a₀" => fun _ : η ↦ DeltaStructure.frobeniusLift E rs
local notation "a₁" => fun _ : η ↦ DeltaStructure.frobeniusLift E rt
local notation "B₀" => DeltaAdjoinDivision E (p : P) a₀

/-- p正則係数環の異なる二根関係のFrobenius像を同時p除算した実raw環はp正則。
各段のghost単射と指定単元δ(p)は明示し、入力関係の正則性は内部で供給する。 -/
theorem deltaRootPairRaw_p_mul_injective
    (hts : t ≠ s)
    (hpA : Function.Injective (fun a : A ↦ (p : A) * a))
    (w : Aˣ) (hw : (w : A) = D.delta (p : A))
    (hg₀ : Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := P) η) → ℕ → RelativeFreeDeltaRing (R := P) η))
    (hg₁ : Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := B₀) η) → ℕ → RelativeFreeDeltaRing (R := B₀) η)) :
    Function.Injective (fun x : DeltaAdjoinDivision E (p : P) (Sum.elim a₀ a₁) ↦
      (p : DeltaAdjoinDivision E (p : P) (Sum.elim a₀ a₁)) * x) := by
  have hpP : Function.Injective (fun f : P ↦ (p : P) * f) := by
    have h : IsSMulRegular A (p : A) := hpA
    have h' := h.of_flat (S := P)
    have h'' : IsSMulRegular P (p : P) := by simpa only [map_natCast] using h'
    exact h''
  let wP := w.map (MvPolynomial.C : A →+* P).toMonoidHom
  have hwP : (wP : P) = (E).delta (p : P) := by
    change MvPolynomial.C (w : A) = _
    rw [hw, ← polynomialRankOneDeltaStructure_delta_C σ D (p : A), map_natCast]
  exact deltaPDivisionPair_p_mul_injective (σ := η) E rs rt hpP hg₀ hg₁ wP hwP
    (deltaRootRelation_modP_isSMulRegular b s)
    (deltaRootRelation_pairPower_modP_isSMulRegular b s t hts)

end SerrePositivity.BhattScholze

end DeltaRootPairRawRegular
