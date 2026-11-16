module

public import SerrePositivity.BhattScholze.Andre.Envelope.NormalizedStep
public import SerrePositivity.BhattScholze.Delta.Division.Witt
public import SerrePositivity.BhattScholze.Andre.Envelope.JetRegularity
public import Mathlib.RingTheory.Regular.Flat
public import SerrePositivity.BhattScholze.Andre.Envelope.RootRelation
public import Mathlib.Data.List.Nodup

/-!
# 有限 δ 関係の Koszul 分解と段の間の Tor

## 概要
下位関係商での次段関係の正則性、一元一般除算の全有限 δ 列の mod (p,d) Koszul 分解、有限根族の次段 Witt 関係・δ 次段関係の有限族の Koszul 分解、同段の部分集合の関係の追加、段の間の射の Koszul 擬同型・射影分解・スカラー塔・Tor。

## 方針
BS 著者版 Corollary 2.44・BS 著者版 Proposition 3.13 の平坦性を Koszul 複体の帰納法で得る部分。

## 規約
係数環・素数・正則性の仮定は各宣言で明示する。

## 使われ方
`Envelope/FamilyEvaluation`、`Envelope/PDivision`、`Envelope/RootResidueKoszul`、`PowerRootEnvelope/DeltaDivisionResidue`、`PowerRootEnvelope/Unconditional/Residue`。
-/

universe u

/-! ## 元の相対自由δ環の具体的下位関係商における次段関係の正則性 -/

@[expose] public noncomputable section DeltaDivisionFiniteJetRegularity

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open _root_.CategoryTheory
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A)
variable (hpA : Function.Injective (fun z : A ↦ (p : A) * z))
variable (hpL : Function.Injective (fun z : RelativeFreeDeltaRing (R := A) σ ↦
  (p : RelativeFreeDeltaRing (R := A) σ) * z))
variable (hg : Function.Injective (WittVector.ghostMap :
  WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
variable (d : A) (a : σ → A) (v : Aˣ) (hv : (v : A) = D.delta d) (N : ℕ)
local notation "L₀" => RelativeFreeDeltaRing (R := A) σ
local notation "I₀" => Ideal.span {(p : L₀), MvPolynomial.C d} ⊔
  deltaDivisionFiniteRelationIdeal D d a (N + 1)
include hpA hpL hg hv

/-- 元の自由δ環の下位関係商内のWitt根関係は非零因子。 -/
theorem Andre.deltaDivisionFiniteWittRelation_quotient_isSMulRegular (s : σ) :
    IsSMulRegular (L₀ ⧸ I₀)
      (Ideal.Quotient.mk I₀ (_root_.SerrePositivity.BhattScholze.deltaDivisionRelativeWittRelationElement D d a v s N)) := by
  let e := _root_.SerrePositivity.BhattScholze.deltaDivisionFiniteNormalizedQuotientEquiv D hpA hpL hg d a v hv N
  have he : e (Ideal.Quotient.mk I₀ (_root_.SerrePositivity.BhattScholze.deltaDivisionRelativeWittRelationElement D d a v s N)) =
      Ideal.Quotient.mk _ (_root_.SerrePositivity.BhattScholze.relativeFreeFiniteInitialPolynomialMap (N + 2) σ A
        (_root_.SerrePositivity.BhattScholze.deltaDivisionWittNormalizedPolynomial D d a v s N)) := by
    dsimp only [e]
    rw [_root_.SerrePositivity.BhattScholze.deltaDivisionFiniteNormalizedQuotientEquiv_mk,
      _root_.SerrePositivity.BhattScholze.deltaDivisionRelativeWittRelationElement_inverse_image D hpA hg]
  have hr := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedAmbientSource_relation_isSMulRegular D d a v N hv s
  intro x y hxy
  apply e.injective
  apply hr
  have h := congrArg e hxy
  simpa only [smul_eq_mul, map_mul, he] using h

/-- 元の自由δ環の下位関係商内で、次のN+2段のδ反復関係は非零因子。 -/
theorem Andre.deltaDivisionFiniteNextJet_quotient_isSMulRegular (s : σ) :
    IsSMulRegular (L₀ ⧸ I₀)
      (Ideal.Quotient.mk I₀ (_root_.SerrePositivity.BhattScholze.deltaDivisionIteratedRelation D d a s (N + 2))) := by
  let E := _root_.SerrePositivity.BhattScholze.relativeFreeDeltaStructure σ D
  let vL := v.map (MvPolynomial.C : A →+* L₀).toMonoidHom
  have hvL : (vL : L₀) = E.delta (MvPolynomial.C d) := by
    change MvPolynomial.C (v : A) = (_root_.SerrePositivity.BhattScholze.relativeFreeDeltaStructure σ D).delta (MvPolynomial.C d)
    rw [hv, _root_.SerrePositivity.BhattScholze.relativeFreeDeltaStructure_delta_C]
  have hpI : (p : L₀) ∈ I₀ :=
    (show Ideal.span {(p : L₀), MvPolynomial.C d} ≤ I₀ from le_sup_left)
      (Ideal.subset_span (by simp))
  have hdI : MvPolynomial.C d ∈ I₀ :=
    (show Ideal.span {(p : L₀), MvPolynomial.C d} ≤ I₀ from le_sup_left)
      (Ideal.subset_span (by simp))
  have hlower : ∀ i ≤ N + 1,
      E.delta^[i] (MvPolynomial.C d * MvPolynomial.X (s, 0) - MvPolynomial.C (a s)) ∈ I₀ := by
    intro i hi
    apply (show _root_.SerrePositivity.BhattScholze.deltaDivisionFiniteRelationIdeal D d a (N + 1) ≤ I₀ from le_sup_right)
    apply Ideal.subset_span
    exact Set.mem_range.mpr ⟨(s, ⟨i, by omega⟩), rfl⟩
  exact (_root_.SerrePositivity.BhattScholze.deltaDivision_next_jet_quotient_isSMulRegular_iff_witt E hpL hg I₀ hpI
    (MvPolynomial.C d) (MvPolynomial.X (s, 0)) (MvPolynomial.C (a s)) hdI vL hvL N hlower).mpr
    (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteWittRelation_quotient_isSMulRegular D hpA hpL hg d a v hv N s)

/-- 元の次段δ反復関係の具体的商上のKoszul分解。添字σの有限性は不要。 -/
theorem Andre.deltaDivisionFiniteNextJet_quotient_isKoszulResolution (s : σ) :
    SerrePositivity.IsKoszulResolution (fun _ : Fin 1 ↦
      Ideal.Quotient.mk I₀ (_root_.SerrePositivity.BhattScholze.deltaDivisionIteratedRelation D d a s (N + 2))) := by
  apply SerrePositivity.isKoszulResolution_of_isWeaklyRegular
  rw [List.ofFn_const, List.replicate_one,
    RingTheory.Sequence.isWeaklyRegular_singleton_iff]
  exact _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNextJet_quotient_isSMulRegular D hpA hpL hg d a v hv N s

/-- 元の次段δ反復関係による導来商は実Koszul錐関手と自然同型。 -/
def Andre.deltaDivisionFiniteNextJet_derivedKoszulNatIso (s : σ) :
    _root_.SerrePositivity.boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span
        {Ideal.Quotient.mk I₀ (_root_.SerrePositivity.BhattScholze.deltaDivisionIteratedRelation D d a s (N + 2))})) ⋙
      _root_.SerrePositivity.boundedAboveDerivedRestrictScalars (Ideal.Quotient.mk (Ideal.span
        {Ideal.Quotient.mk I₀ (_root_.SerrePositivity.BhattScholze.deltaDivisionIteratedRelation D d a s (N + 2))})) ⋙
      DerivedCategory.Minus.ι ≅
    DerivedCategory.Minus.ι ⋙ _root_.SerrePositivity.DerivedCompletion.derivedScalarConeFunctor (L₀ ⧸ I₀)
      (Ideal.Quotient.mk I₀ (_root_.SerrePositivity.BhattScholze.deltaDivisionIteratedRelation D d a s (N + 2))) :=
  _root_.SerrePositivity.restrictedDerivedQuotientKoszulNatIso _
    (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNextJet_quotient_isSMulRegular D hpA hpL hg d a v hv N s)

end SerrePositivity.BhattScholze

end DeltaDivisionFiniteJetRegularity

/-! ## 一元一般除算の全有限δ列のmod(p,d)Koszul分解

初項の正則性と既存の初期・高段の正則性を合成する。
通常のmod(p,d)商上の計算であり、実導来完備化後の平坦性は結論しない。
-/

@[expose] public noncomputable section DeltaDivisionFiniteResidueKoszul

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (d : A) (a : σ → A)
local notation "L₀" => RelativeFreeDeltaRing (R := A) σ
local notation "B₀" => Ideal.span {(p : L₀), MvPolynomial.C d}
local notation "R₀" => L₀ ⧸ B₀
local notation "q₀" => Ideal.Quotient.mk B₀
local notation "I₀" => deltaDivisionFiniteRelationIdeal D d a

/-- mod(p,d)で有限δ関係を課す二重商と、元の自由環の実有限剰余商との標準比較。 -/
def Andre.deltaDivisionFiniteResidueQuotientEquiv (N : ℕ) :
    (R₀ ⧸ (I₀ N).map q₀) ≃+* (L₀ ⧸ (B₀ ⊔ I₀ N)) :=
  DoubleQuot.quotQuotEquivQuotSup B₀ (I₀ N)

/-- 二重商比較は元の自由環の標準像を保つ。 -/
theorem Andre.deltaDivisionFiniteResidueQuotientEquiv_mk (N : ℕ) (f : L₀) :
    _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteResidueQuotientEquiv D d a N
      (Ideal.Quotient.mk ((I₀ N).map q₀) (q₀ f)) = Ideal.Quotient.mk (B₀ ⊔ I₀ N) f :=
  DoubleQuot.quotQuotEquivQuotSup_quotQuotMk B₀ (I₀ N) f

variable [Unique σ]
local notation "g₀" => deltaDivisionIteratedRelation D d a (default : σ)

/-- 一元有限δ列の実mod(p,d)像の生成イデアルは、既存の有限関係イデアルの像。 -/
theorem Andre.deltaDivisionFiniteResidueRelations_ofList (N : ℕ) :
    Ideal.ofList (List.ofFn fun i : Fin (N + 1) => q₀ (g₀ i.val)) = (I₀ N).map q₀ := by
  unfold _root_.SerrePositivity.BhattScholze.deltaDivisionFiniteRelationIdeal
  rw [Ideal.map_span, ← Set.range_comp']
  apply congrArg Ideal.span
  ext z
  simp only [List.mem_ofFn, Set.mem_ofPred_eq, Set.mem_range]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨(default, i), rfl⟩
  · rintro ⟨⟨s, i⟩, rfl⟩
    have hs : s = (default : σ) := Subsingleton.elim _ _
    subst s
    exact ⟨i, rfl⟩

/-- 初期と高段の正規化を合成し、実mod(p,d)有限前段商上の次δ関係の正則性を得る。 -/
theorem Andre.deltaDivisionFiniteResidueNext_isSMulRegular
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (hpL : Function.Injective (fun x : L₀ => (p : L₀) * x))
    (hg : Function.Injective (WittVector.ghostMap : WittVector p L₀ → ℕ → L₀))
    (v : Aˣ) (hv : (v : A) = D.delta d) (N : ℕ) :
    IsSMulRegular (R₀ ⧸ (I₀ N).map q₀)
      (Ideal.Quotient.mk ((I₀ N).map q₀) (q₀ (g₀ (N + 1)))) := by
  have hr : IsSMulRegular (L₀ ⧸ (B₀ ⊔ I₀ N))
      (Ideal.Quotient.mk (B₀ ⊔ I₀ N) (g₀ (N + 1))) := by
    cases N with
    | zero => exact _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFirstJet_residue_isSMulRegular D d a v hv default
    | succ n =>
        exact _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNextJet_quotient_isSMulRegular D hpA hpL hg d a v hv n default
  let e := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteResidueQuotientEquiv D d a N
  have he : e (Ideal.Quotient.mk ((I₀ N).map q₀) (q₀ (g₀ (N + 1)))) =
      Ideal.Quotient.mk (B₀ ⊔ I₀ N) (g₀ (N + 1)) :=
    _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteResidueQuotientEquiv_mk D d a N _
  intro x y hxy
  apply e.injective
  apply hr
  have h := congrArg e hxy
  simpa only [smul_eq_mul, map_mul, he] using h

/-- 初項が正則なら、一般dの実mod(p,d)反復δ列の全有限prefixは弱正則。 -/
theorem Andre.deltaDivisionFiniteResidueRelations_isWeaklyRegular
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (hpL : Function.Injective (fun x : L₀ => (p : L₀) * x))
    (hg : Function.Injective (WittVector.ghostMap : WittVector p L₀ → ℕ → L₀))
    (v : Aˣ) (hv : (v : A) = D.delta d)
    (h0 : IsSMulRegular R₀ (q₀ (g₀ 0))) (N : ℕ) :
    RingTheory.Sequence.IsWeaklyRegular R₀
      (List.ofFn fun i : Fin (N + 1) => q₀ (g₀ i.val)) := by
  induction N with
  | zero =>
      rw [List.ofFn_succ, List.ofFn_zero,
        RingTheory.Sequence.isWeaklyRegular_singleton_iff]
      exact h0
  | succ N ih =>
      rw [List.ofFn_succ', List.concat_eq_append,
        RingTheory.Sequence.isWeaklyRegular_append_iff]
      refine ⟨ih, ?_⟩
      rw [RingTheory.Sequence.isWeaklyRegular_singleton_iff]
      have hI : (Ideal.ofList (List.ofFn fun i : Fin (N + 1) => q₀ (g₀ i.val)) • ⊤ :
          Submodule R₀ R₀) = (I₀ N).map q₀ := by
        rw [Ideal.smul_eq_mul, Ideal.mul_top, _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteResidueRelations_ofList]
      change IsSMulRegular (R₀ ⧸
        (Ideal.ofList (List.ofFn fun i : Fin (N + 1) => q₀ (g₀ i.val)) • ⊤ : Submodule R₀ R₀))
        (q₀ (g₀ (N + 1)))
      rw [hI]
      exact (isSMulRegular_map (Ideal.Quotient.mk ((I₀ N).map q₀)) (fun _ => rfl)).mp
        (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteResidueNext_isSMulRegular D d a hpA hpL hg v hv N)

/-- 全有限δ深さの実mod(p,d)Koszul複体は、対応する実通常商を分解する。 -/
theorem Andre.deltaDivisionFiniteResidueRelations_isKoszulResolution
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (hpL : Function.Injective (fun x : L₀ => (p : L₀) * x))
    (hg : Function.Injective (WittVector.ghostMap : WittVector p L₀ → ℕ → L₀))
    (v : Aˣ) (hv : (v : A) = D.delta d)
    (h0 : IsSMulRegular R₀ (q₀ (g₀ 0))) (N : ℕ) :
    SerrePositivity.IsKoszulResolution (fun i : Fin (N + 1) => q₀ (g₀ i.val)) :=
  SerrePositivity.isKoszulResolution_of_isWeaklyRegular _
    (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteResidueRelations_isWeaklyRegular D d a hpA hpL hg v hv h0 N)

end SerrePositivity.BhattScholze

end DeltaDivisionFiniteResidueKoszul

/-! ## 任意有限根族の次段Witt関係の実残余Koszul分解 -/

@[expose] public noncomputable section DeltaDivisionFiniteWittFamilyKoszul

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (d : A) (a : σ → A) (v : Aˣ) (N : ℕ)
local notation "L₀" => RelativeFreeDeltaRing (R := A) σ
local notation "J" => deltaDivisionFirstResidueIdeal D d a ⊔
  deltaDivisionFiniteNormalizedWittIdeal D d a v N
local notation "S₀" => MvPolynomial (σ × Fin (N + 2)) A ⧸
  _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepSourceIdeal D d a v N
local notation "I₀" => Ideal.span {(p : L₀), MvPolynomial.C d} ⊔
  deltaDivisionFiniteRelationIdeal D d a (N + 1)

/-- 後続変数を残す実正規化商でも、異なる有限個の次段関係は弱正則。 -/
theorem Andre.deltaDivisionNormalizedAmbientSource_fin_isWeaklyRegular
    (hv : (v : A) = D.delta d) {m : ℕ} (s : Fin m → σ)
    (hs : Function.Injective s) :
    RingTheory.Sequence.IsWeaklyRegular (L₀ ⧸ J)
      (List.ofFn fun i => Ideal.Quotient.mk J
        (_root_.SerrePositivity.BhattScholze.relativeFreeFiniteInitialPolynomialMap (N + 2) σ A
          (_root_.SerrePositivity.BhattScholze.deltaDivisionWittNormalizedPolynomial D d a v (s i) N))) := by
  let e := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedAmbientSourceEquiv D d a v N hv
  let rs := List.ofFn fun i => Ideal.Quotient.mk J
    (_root_.SerrePositivity.BhattScholze.relativeFreeFiniteInitialPolynomialMap (N + 2) σ A
      (_root_.SerrePositivity.BhattScholze.deltaDivisionWittNormalizedPolynomial D d a v (s i) N))
  have hr := (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepSourceRelation_fin_isWeaklyRegular
    D d a v N s hs).of_flat (S := MvPolynomial (σ × ℕ) S₀)
  refine (e.toAddEquiv.isWeaklyRegular_congr (as := rs) (bs := rs.map e) ?_).mpr ?_
  · apply List.forall₂_map_right_iff.mpr
    apply List.forall₂_same.mpr
    intro r _ x
    exact e.map_mul r x
  · simpa only [rs, List.map_ofFn, Function.comp_def, e,
      _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedAmbientSourceEquiv_initial, MvPolynomial.algebraMap_eq] using hr

/-- 同じ実正規化商で、次段Witt有限族のKoszul複体は通常商を分解する。 -/
theorem Andre.deltaDivisionNormalizedAmbientSource_fin_isKoszulResolution
    (hv : (v : A) = D.delta d) {m : ℕ} (s : Fin m → σ)
    (hs : Function.Injective s) :
    SerrePositivity.IsKoszulResolution (fun i => Ideal.Quotient.mk J
      (_root_.SerrePositivity.BhattScholze.relativeFreeFiniteInitialPolynomialMap (N + 2) σ A
        (_root_.SerrePositivity.BhattScholze.deltaDivisionWittNormalizedPolynomial D d a v (s i) N))) :=
  SerrePositivity.isKoszulResolution_of_isWeaklyRegular _
    (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedAmbientSource_fin_isWeaklyRegular D d a v N hv s hs)

variable (hpA : Function.Injective (fun z : A => (p : A) * z))
variable (hpL : Function.Injective (fun z : RelativeFreeDeltaRing (R := A) σ =>
  (p : RelativeFreeDeltaRing (R := A) σ) * z))
variable (hg : Function.Injective (WittVector.ghostMap :
  WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ →
    RelativeFreeDeltaRing (R := A) σ))
include hpA hpL hg

/-- 元の自由δ環の実下位関係商でも、次段Witt有限族は弱正則。 -/
theorem Andre.deltaDivisionFiniteWittRelation_quotient_fin_isWeaklyRegular
    (hv : (v : A) = D.delta d) {m : ℕ} (s : Fin m → σ)
    (hs : Function.Injective s) :
    RingTheory.Sequence.IsWeaklyRegular (L₀ ⧸ I₀)
      (List.ofFn fun i => Ideal.Quotient.mk I₀
        (_root_.SerrePositivity.BhattScholze.deltaDivisionRelativeWittRelationElement D d a v (s i) N)) := by
  let e := _root_.SerrePositivity.BhattScholze.deltaDivisionFiniteNormalizedQuotientEquiv D hpA hpL hg d a v hv N
  let rs := List.ofFn fun i => Ideal.Quotient.mk I₀
    (_root_.SerrePositivity.BhattScholze.deltaDivisionRelativeWittRelationElement D d a v (s i) N)
  have he (t : σ) : e (Ideal.Quotient.mk I₀
      (_root_.SerrePositivity.BhattScholze.deltaDivisionRelativeWittRelationElement D d a v t N)) =
      Ideal.Quotient.mk J (_root_.SerrePositivity.BhattScholze.relativeFreeFiniteInitialPolynomialMap (N + 2) σ A
        (_root_.SerrePositivity.BhattScholze.deltaDivisionWittNormalizedPolynomial D d a v t N)) := by
    dsimp only [e]
    rw [_root_.SerrePositivity.BhattScholze.deltaDivisionFiniteNormalizedQuotientEquiv_mk,
      _root_.SerrePositivity.BhattScholze.deltaDivisionRelativeWittRelationElement_inverse_image D hpA hg]
  refine (e.toAddEquiv.isWeaklyRegular_congr (as := rs) (bs := rs.map e) ?_).mpr ?_
  · apply List.forall₂_map_right_iff.mpr
    apply List.forall₂_same.mpr
    intro r _ x
    exact e.map_mul r x
  · simpa only [rs, List.map_ofFn, Function.comp_def, he] using
      _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedAmbientSource_fin_isWeaklyRegular D d a v N hv s hs

/-- 元の実商上の次段Witt有限族は、実通常商のKoszul分解を与える。 -/
theorem Andre.deltaDivisionFiniteWittRelation_quotient_fin_isKoszulResolution
    (hv : (v : A) = D.delta d) {m : ℕ} (s : Fin m → σ)
    (hs : Function.Injective s) :
    SerrePositivity.IsKoszulResolution (fun i => Ideal.Quotient.mk I₀
      (_root_.SerrePositivity.BhattScholze.deltaDivisionRelativeWittRelationElement D d a v (s i) N)) :=
  SerrePositivity.isKoszulResolution_of_isWeaklyRegular _
    (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteWittRelation_quotient_fin_isWeaklyRegular
      D d a v N hpA hpL hg hv s hs)

end SerrePositivity.BhattScholze

end DeltaDivisionFiniteWittFamilyKoszul

/-! ## 元のδ次段関係の任意有限族の実残余Koszul分解 -/

@[expose] public noncomputable section DeltaDivisionFiniteJetFamilyKoszul

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A)
variable (hpA : Function.Injective (fun z : A => (p : A) * z))
variable (hpL : Function.Injective (fun z : RelativeFreeDeltaRing (R := A) σ =>
  (p : RelativeFreeDeltaRing (R := A) σ) * z))
variable (hg : Function.Injective (WittVector.ghostMap :
  WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ →
    RelativeFreeDeltaRing (R := A) σ))
variable (d : A) (a : σ → A) (v : Aˣ) (hv : (v : A) = D.delta d) (N : ℕ)
local notation "L₀" => RelativeFreeDeltaRing (R := A) σ
local notation "I₀" => Ideal.span {(p : L₀), MvPolynomial.C d} ⊔
  deltaDivisionFiniteRelationIdeal D d a (N + 1)
include hpA hpL hg hv

/-- 実下位関係商で、異なる有限個の元のδ次段関係は弱正則列。 -/
theorem Andre.deltaDivisionFiniteNextJet_quotient_fin_isWeaklyRegular
    {m : ℕ} (s : Fin m → σ) (hs : Function.Injective s) :
    RingTheory.Sequence.IsWeaklyRegular (L₀ ⧸ I₀)
      (List.ofFn fun i => Ideal.Quotient.mk I₀
        (_root_.SerrePositivity.BhattScholze.deltaDivisionIteratedRelation D d a (s i) (N + 2))) := by
  let E := _root_.SerrePositivity.BhattScholze.relativeFreeDeltaStructure σ D
  let vL := v.map (MvPolynomial.C : A →+* L₀).toMonoidHom
  have hvL : (vL : L₀) = E.delta (MvPolynomial.C d) := by
    change MvPolynomial.C (v : A) = _
    rw [hv, _root_.SerrePositivity.BhattScholze.relativeFreeDeltaStructure_delta_C]
  let f : σ → L₀ ⧸ I₀ := fun t => Ideal.Quotient.mk I₀
    (_root_.SerrePositivity.BhattScholze.deltaDivisionIteratedRelation D d a t (N + 2))
  let g : σ → L₀ ⧸ I₀ := fun t => Ideal.Quotient.mk I₀
    (_root_.SerrePositivity.BhattScholze.deltaDivisionRelativeWittRelationElement D d a v t N)
  have hspan (t : σ) : Ideal.span {f t} = Ideal.span {g t} := by
    apply _root_.SerrePositivity.BhattScholze.deltaDivision_next_jet_quotient_span_eq_witt E hpL hg I₀
      ((show Ideal.span {(p : L₀), MvPolynomial.C d} ≤ I₀ from le_sup_left)
        (Ideal.subset_span (by simp))) (MvPolynomial.C d)
      (MvPolynomial.X (t, 0)) (MvPolynomial.C (a t))
      ((show Ideal.span {(p : L₀), MvPolynomial.C d} ≤ I₀ from le_sup_left)
        (Ideal.subset_span (by simp))) vL hvL N
    intro i hi
    apply (show _root_.SerrePositivity.BhattScholze.deltaDivisionFiniteRelationIdeal D d a (N + 1) ≤ I₀ from le_sup_right)
    apply Ideal.subset_span
    exact Set.mem_range.mpr ⟨(t, ⟨i, by omega⟩), rfl⟩
  have hI (l : List σ) : Ideal.ofList (l.map f) = Ideal.ofList (l.map g) := by
    induction l with
    | nil => rfl
    | cons t l ih => simp only [List.map_cons, Ideal.ofList_cons, hspan, ih]
  have hr := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteWittRelation_quotient_fin_isWeaklyRegular
    D d a v N hpA hpL hg hv s hs
  change RingTheory.Sequence.IsWeaklyRegular (L₀ ⧸ I₀) (List.ofFn fun i => f (s i))
  constructor
  intro i hi
  have hi' : i < m := by simpa only [List.length_ofFn] using hi
  have hw := hr.regular_mod_prev i (by simpa only [List.length_ofFn] using hi')
  have hprefix : Ideal.ofList ((List.ofFn fun j => f (s j)).take i) =
      Ideal.ofList ((List.ofFn fun j => g (s j)).take i) := by
    simpa only [List.map_take, List.map_ofFn, Function.comp_def] using
      hI ((List.ofFn s).take i)
  rw [hprefix]
  simp only [List.getElem_ofFn] at hw ⊢
  change IsSMulRegular
    ((L₀ ⧸ I₀) ⧸ (Ideal.ofList ((List.ofFn fun j => g (s j)).take i) • ⊤ :
      Submodule (L₀ ⧸ I₀) (L₀ ⧸ I₀))) (f (s ⟨i, hi'⟩))
  change IsSMulRegular
    ((L₀ ⧸ I₀) ⧸ (Ideal.ofList ((List.ofFn fun j => g (s j)).take i) • ⊤ :
      Submodule (L₀ ⧸ I₀) (L₀ ⧸ I₀))) (g (s ⟨i, hi'⟩)) at hw
  have hm : g (s ⟨i, hi'⟩) ∈ Ideal.span {f (s ⟨i, hi'⟩)} :=
    (hspan _).symm ▸ Ideal.mem_span_singleton_self _
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hm
  intro x y hxy
  apply hw
  change g (s ⟨i, hi'⟩) • x = g (s ⟨i, hi'⟩) • y
  change f (s ⟨i, hi'⟩) • x = f (s ⟨i, hi'⟩) • y at hxy
  rw [hc, mul_comm, mul_smul, mul_smul, hxy]

/-- 同じ実下位関係商上で、実δ次段有限族は通常商のKoszul分解を与える。 -/
theorem Andre.deltaDivisionFiniteNextJet_quotient_fin_isKoszulResolution
    {m : ℕ} (s : Fin m → σ) (hs : Function.Injective s) :
    SerrePositivity.IsKoszulResolution (fun i => Ideal.Quotient.mk I₀
      (_root_.SerrePositivity.BhattScholze.deltaDivisionIteratedRelation D d a (s i) (N + 2))) :=
  SerrePositivity.isKoszulResolution_of_isWeaklyRegular _
    (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNextJet_quotient_fin_isWeaklyRegular D hpA hpL hg d a v hv N s hs)

end SerrePositivity.BhattScholze

end DeltaDivisionFiniteJetFamilyKoszul

/-! ## 同段の任意部分集合のδ関係を追加した実商の比較 -/

@[expose] public noncomputable section DeltaDivisionFiniteJetSubset

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A)
variable (hpA : Function.Injective (fun z : A ↦ (p : A) * z))
variable (hpL : Function.Injective (fun z : RelativeFreeDeltaRing (R := A) σ ↦
  (p : RelativeFreeDeltaRing (R := A) σ) * z))
variable (hg : Function.Injective (WittVector.ghostMap :
  WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
variable (d : A) (a : σ → A) (v : Aˣ) (hv : (v : A) = D.delta d) (N : ℕ)
local notation "L₀" => RelativeFreeDeltaRing (R := A) σ
local notation "I₀" => Ideal.span {(p : L₀), MvPolynomial.C d} ⊔
  deltaDivisionFiniteRelationIdeal D d a (N + 1)
local notation "R₀" => L₀ ⧸ I₀
local notation "Q₀" => _root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionFiniteNormalizedQuotient D d a v N
local notation "b₀" => _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedStepCoefficients D d a v N
local notation "f₀" => fun s : σ ↦ Ideal.Quotient.mk I₀
  (deltaDivisionIteratedRelation D d a s (N + 2))
local notation "w₀" => fun s : σ ↦ Ideal.Quotient.mk I₀
  (deltaDivisionRelativeWittRelationElement D d a v s N)

/-- 元の下位δ関係商を最高変数・後続変数を分離した実多項式環へ送る同型。 -/
def Andre.deltaDivisionFiniteJetSourceEquiv : R₀ ≃+* MvPolynomial (σ × ℕ) (MvPolynomial σ Q₀) :=
  ((_root_.SerrePositivity.BhattScholze.deltaDivisionFiniteNormalizedQuotientEquiv D hpA hpL hg d a v hv N).trans
    (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedAmbientSourceEquiv D d a v N hv)).trans
    (MvPolynomial.mapEquiv (σ × ℕ) (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepSourceQuotientEquiv D d a v N))

/-- 元のWitt根関係は、最高変数の実根関係の係数像に移る。 -/
theorem Andre.deltaDivisionFiniteJetSourceEquiv_witt (s : σ) :
    _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteJetSourceEquiv D hpA hpL hg d a v hv N (w₀ s) =
      MvPolynomial.C (_root_.SerrePositivity.BhattScholze.Andre.deltaRootRelationFamily (p := p) b₀ s) := by
  unfold _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteJetSourceEquiv
  rw [RingEquiv.trans_apply, RingEquiv.trans_apply,
    _root_.SerrePositivity.BhattScholze.deltaDivisionFiniteNormalizedQuotientEquiv_mk,
    _root_.SerrePositivity.BhattScholze.deltaDivisionRelativeWittRelationElement_inverse_image D hpA hg,
    _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedAmbientSourceEquiv_initial, MvPolynomial.mapEquiv_apply,
    MvPolynomial.map_C, RingEquiv.coe_toRingHom,
    _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepSourceQuotientEquiv_mk,
    _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepPolynomialMap_relation]

include hpL hg hv in
/-- 下位商内では、任意部分集合の次段δ関係とWitt根関係が同じイデアルを生成する。 -/
theorem Andre.deltaDivisionFiniteJetSubset_span_eq_witt (T : Set σ) :
    Ideal.span (Set.range fun s : T ↦ f₀ s) =
      Ideal.span (Set.range fun s : T ↦ w₀ s) := by
  let E := _root_.SerrePositivity.BhattScholze.relativeFreeDeltaStructure σ D
  let vL := v.map (MvPolynomial.C : A →+* L₀).toMonoidHom
  have hvL : (vL : L₀) = E.delta (MvPolynomial.C d) := by
    change MvPolynomial.C (v : A) = (_root_.SerrePositivity.BhattScholze.relativeFreeDeltaStructure σ D).delta (MvPolynomial.C d)
    rw [hv, _root_.SerrePositivity.BhattScholze.relativeFreeDeltaStructure_delta_C]
  have hpI : (p : L₀) ∈ I₀ :=
    (show Ideal.span {(p : L₀), MvPolynomial.C d} ≤ I₀ from le_sup_left)
      (Ideal.subset_span (by simp))
  have hdI : MvPolynomial.C d ∈ I₀ :=
    (show Ideal.span {(p : L₀), MvPolynomial.C d} ≤ I₀ from le_sup_left)
      (Ideal.subset_span (by simp))
  have hlower : ∀ s : T, ∀ i ≤ N + 1,
      E.delta^[i] (MvPolynomial.C d * MvPolynomial.X ((s : σ), 0) - MvPolynomial.C (a s)) ∈ I₀ := by
    intro s i hi
    apply (show _root_.SerrePositivity.BhattScholze.deltaDivisionFiniteRelationIdeal D d a (N + 1) ≤ I₀ from le_sup_right)
    exact Ideal.subset_span (Set.mem_range.mpr ⟨((s : σ), ⟨i, by omega⟩), rfl⟩)
  have h := congrArg (Ideal.map (Ideal.Quotient.mk I₀))
    (_root_.SerrePositivity.BhattScholze.deltaDivision_family_next_jets_sup_span_eq_witt_relations E hpL hg I₀ hpI
      (MvPolynomial.C d) (fun s : T ↦ MvPolynomial.X ((s : σ), 0))
      (fun s : T ↦ MvPolynomial.C (a s)) hdI vL hvL N hlower)
  rw [Ideal.map_sup, Ideal.map_quotient_self, bot_sup_eq] at h
  rw [Ideal.map_sup, Ideal.map_quotient_self, bot_sup_eq] at h
  simpa [Ideal.map_span, ← Set.range_comp', E, vL,
    _root_.SerrePositivity.BhattScholze.deltaDivisionIteratedRelation, _root_.SerrePositivity.BhattScholze.deltaDivisionRelativeWittRelationElement] using h

/-- 次段δ関係の部分集合イデアルは、実部分根関係イデアルの係数包含像に移る。 -/
theorem Andre.deltaDivisionFiniteJetSubset_map_source (T : Set σ) :
    (Ideal.span (Set.range fun s : T ↦ f₀ s)).map
      (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteJetSourceEquiv D hpA hpL hg d a v hv N).toRingHom =
    (_root_.SerrePositivity.BhattScholze.Andre.deltaRootSubsetRelationIdeal (p := p) T b₀).map
      (MvPolynomial.C : MvPolynomial σ Q₀ →+* MvPolynomial (σ × ℕ) (MvPolynomial σ Q₀)) := by
  rw [_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteJetSubset_span_eq_witt D hpL hg d a v hv N T]
  simp only [Ideal.map_span, ← Set.range_comp', _root_.SerrePositivity.BhattScholze.Andre.deltaRootSubsetRelationIdeal,
    RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteJetSourceEquiv_witt]

/-- 任意先行添字集合の次段δ関係を追加した実商の具体的多項式表示。 -/
def Andre.deltaDivisionFiniteJetSubsetQuotientEquiv (T : Set σ) :
    (R₀ ⧸ Ideal.span (Set.range fun s : T ↦ f₀ s)) ≃+*
      MvPolynomial (σ × ℕ) (MvPolynomial σ Q₀ ⧸ _root_.SerrePositivity.BhattScholze.Andre.deltaRootSubsetRelationIdeal (p := p) T b₀) :=
  (Ideal.quotientEquiv _ _ (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteJetSourceEquiv D hpA hpL hg d a v hv N)
    (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteJetSubset_map_source D hpA hpL hg d a v hv N T).symm).trans
    (MvPolynomial.quotientEquivQuotientMvPolynomial (σ := σ × ℕ)
      (_root_.SerrePositivity.BhattScholze.Andre.deltaRootSubsetRelationIdeal (p := p) T b₀)).symm.toRingEquiv

/-- 部分集合商の同型は、残るWitt関係の標準像を根関係商の係数像へ送る。 -/
theorem Andre.deltaDivisionFiniteJetSubsetQuotientEquiv_witt (T : Set σ) (s : σ) :
    _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteJetSubsetQuotientEquiv D hpA hpL hg d a v hv N T
      (Ideal.Quotient.mk _ (w₀ s)) =
      MvPolynomial.C (Ideal.Quotient.mk (_root_.SerrePositivity.BhattScholze.Andre.deltaRootSubsetRelationIdeal (p := p) T b₀)
        (_root_.SerrePositivity.BhattScholze.Andre.deltaRootRelationFamily (p := p) b₀ s)) := by
  unfold _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteJetSubsetQuotientEquiv
  rw [RingEquiv.trans_apply, Ideal.quotientEquiv_mk,
    _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteJetSourceEquiv_witt]
  change MvPolynomial.eval₂Hom
    (MvPolynomial.C.comp (Ideal.Quotient.mk (_root_.SerrePositivity.BhattScholze.Andre.deltaRootSubsetRelationIdeal (p := p) T b₀)))
    MvPolynomial.X (MvPolynomial.C (_root_.SerrePositivity.BhattScholze.Andre.deltaRootRelationFamily (p := p) b₀ s)) = _
  exact MvPolynomial.eval₂Hom_C _ _ _

include hpA hpL hg hv in
/-- 任意先行部分集合を課しても、集合外のWitt根関係の像は非零因子。 -/
theorem Andre.deltaDivisionFiniteJetSubset_witt_isSMulRegular (T : Set σ) (s : σ) (hs : s ∉ T) :
    IsSMulRegular (R₀ ⧸ Ideal.span (Set.range fun t : T ↦ f₀ t))
      (Ideal.Quotient.mk (Ideal.span (Set.range fun t : T ↦ f₀ t)) (w₀ s)) := by
  have hr := _root_.SerrePositivity.BhattScholze.Andre.deltaRootSubsetQuotient_remaining_isSMulRegular (p := p) T b₀ s hs
  let e := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteJetSubsetQuotientEquiv D hpA hpL hg d a v hv N T
  have he : e (Ideal.Quotient.mk _ (w₀ s)) =
      MvPolynomial.C (Ideal.Quotient.mk (_root_.SerrePositivity.BhattScholze.Andre.deltaRootSubsetRelationIdeal (p := p) T b₀)
        (_root_.SerrePositivity.BhattScholze.Andre.deltaRootRelationFamily (p := p) b₀ s)) :=
    _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteJetSubsetQuotientEquiv_witt D hpA hpL hg d a v hv N T s
  intro x y hxy
  apply e.injective
  apply MvPolynomial.ext
  intro k
  apply hr
  have h := congrArg (fun z ↦ (e z).coeff k) hxy
  simpa only [smul_eq_mul, map_mul, he, MvPolynomial.coeff_C_mul] using h

include hpA hpL hg hv in
/-- 任意先行部分集合を課しても、集合外の元の次段δ関係の像は非零因子。 -/
theorem Andre.deltaDivisionFiniteJetSubset_next_isSMulRegular (T : Set σ) (s : σ) (hs : s ∉ T) :
    IsSMulRegular (R₀ ⧸ Ideal.span (Set.range fun t : T ↦ f₀ t))
      (Ideal.Quotient.mk (Ideal.span (Set.range fun t : T ↦ f₀ t)) (f₀ s)) := by
  have hrange (g : σ → R₀) : Set.range (fun t : ({s} : Set σ) ↦ g t) = {g s} := by
    ext x
    constructor
    · rintro ⟨t, rfl⟩
      have ht : (t : σ) = s := t.property
      simp only [ht, Set.mem_singleton_iff]
    · intro hx
      obtain rfl := Set.mem_singleton_iff.mp hx
      exact ⟨⟨s, rfl⟩, rfl⟩
  have he := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteJetSubset_span_eq_witt D hpL hg d a v hv N ({s} : Set σ)
  rw [hrange f₀, hrange w₀] at he
  have h := congrArg (Ideal.map (Ideal.Quotient.mk
    (Ideal.span (Set.range fun t : T ↦ f₀ t)))) he
  simp only [Ideal.map_span, Set.image_singleton] at h
  have hm : Ideal.Quotient.mk (Ideal.span (Set.range fun t : T ↦ f₀ t)) (w₀ s) ∈
      Ideal.span {Ideal.Quotient.mk (Ideal.span (Set.range fun t : T ↦ f₀ t)) (f₀ s)} :=
    h.symm ▸ Ideal.mem_span_singleton_self _
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hm
  have hw : IsRegular (Ideal.Quotient.mk (Ideal.span (Set.range fun t : T ↦ f₀ t)) (w₀ s)) :=
    isLeftRegular_iff_isRegular.mp
      (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteJetSubset_witt_isSMulRegular D hpA hpL hg d a v hv N T s hs)
  rw [hc] at hw
  exact hw.of_mul_left.left

end SerrePositivity.BhattScholze

end DeltaDivisionFiniteJetSubset

/-! ## 元の同段δ関係の有限族の弱正則性と実Koszul分解 -/

@[expose] public noncomputable section DeltaDivisionFiniteJetFamilyRegularity

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A)
variable (hpA : Function.Injective (fun z : A ↦ (p : A) * z))
variable (hpL : Function.Injective (fun z : RelativeFreeDeltaRing (R := A) σ ↦
  (p : RelativeFreeDeltaRing (R := A) σ) * z))
variable (hg : Function.Injective (WittVector.ghostMap :
  WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
variable (d : A) (a : σ → A) (v : Aˣ) (hv : (v : A) = D.delta d) (N : ℕ)
local notation "L₀" => RelativeFreeDeltaRing (R := A) σ
local notation "I₀" => Ideal.span {(p : L₀), MvPolynomial.C d} ⊔
  deltaDivisionFiniteRelationIdeal D d a (N + 1)
local notation "R₀" => L₀ ⧸ I₀
local notation "f₀" => fun s : σ ↦ Ideal.Quotient.mk I₀
  (deltaDivisionIteratedRelation D d a s (N + 2))

/-- 元の同段δ関係の有限列のイデアルは、その添字部分集合の関係イデアル。 -/
theorem Andre.deltaDivisionFiniteJet_ofList_eq_span (l : List σ) :
    Ideal.ofList (l.map f₀) = Ideal.span (Set.range fun s : {s | s ∈ l} ↦ f₀ s) := by
  rw [Ideal.ofList]
  congr 1
  ext x
  simp only [Set.mem_ofPred_eq, List.mem_map, Set.mem_range]
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact ⟨⟨s, hs⟩, rfl⟩
  · rintro ⟨s, rfl⟩
    exact ⟨s, s.property, rfl⟩

include hpA hpL hg hv

/-- 元の下位関係商内の、重複しない有限同段δ関係列は弱正則。 -/
theorem Andre.deltaDivisionFiniteJet_list_isWeaklyRegular (l : List σ) (hl : l.Nodup) :
    RingTheory.Sequence.IsWeaklyRegular R₀ (l.map f₀) := by
  constructor
  intro i hi
  have hi' : i < l.length := by simpa only [List.length_map] using hi
  have hs : l[i] ∉ l.take i := by
    intro hm
    obtain ⟨j, hj, hji⟩ := List.mem_iff_getElem.mp hm
    rw [List.getElem_take] at hji
    have he := hl.getElem_inj_iff.mp hji
    have hj' : j < i := lt_of_lt_of_le hj (List.length_take_le _ _)
    omega
  have h := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteJetSubset_next_isSMulRegular
    D hpA hpL hg d a v hv N {s | s ∈ l.take i} l[i] hs
  have hr : IsSMulRegular
      (R₀ ⧸ Ideal.span (Set.range fun s : {s | s ∈ l.take i} ↦ f₀ s)) (f₀ l[i]) :=
    (isSMulRegular_map (Ideal.Quotient.mk _) (fun _ ↦ rfl)).mp h
  have hI : (Ideal.ofList ((l.map f₀).take i) • ⊤ : Submodule R₀ R₀) =
      Ideal.span (Set.range fun s : {s | s ∈ l.take i} ↦ f₀ s) := by
    rw [Ideal.smul_eq_mul, Ideal.mul_top, ← List.map_take,
      _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteJet_ofList_eq_span]
  rw [hI, List.getElem_map]
  exact hr

/-- Fin mの単射で指定する元の同段δ関係の有限族は弱正則。 -/
theorem Andre.deltaDivisionFiniteJet_fin_isWeaklyRegular {m : ℕ}
    (s : Fin m → σ) (hs : Function.Injective s) :
    RingTheory.Sequence.IsWeaklyRegular R₀ (List.ofFn fun i ↦ f₀ (s i)) := by
  simpa only [List.map_ofFn, Function.comp_def] using
    _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteJet_list_isWeaklyRegular D hpA hpL hg d a v hv N
      (List.ofFn s) (List.nodup_ofFn_ofInjective hs)

/-- 元の同段δ関係の異なる有限族は、具体的下位商上の実Koszul分解を与える。 -/
theorem Andre.deltaDivisionFiniteJet_fin_isKoszulResolution {m : ℕ}
    (s : Fin m → σ) (hs : Function.Injective s) :
    SerrePositivity.IsKoszulResolution (fun i ↦ f₀ (s i)) :=
  SerrePositivity.isKoszulResolution_of_isWeaklyRegular _
    (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteJet_fin_isWeaklyRegular D hpA hpL hg d a v hv N s hs)

/-- 有限添字の場合、元の全同段δ関係は具体的下位商上の実Koszul分解を与える。 -/
theorem Andre.deltaDivisionFiniteJet_all_isKoszulResolution [Fintype σ] :
    SerrePositivity.IsKoszulResolution
      (fun i : Fin (Fintype.card σ) ↦ f₀ ((Fintype.equivFin σ).symm i)) :=
  _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteJet_fin_isKoszulResolution D hpA hpL hg d a v hv N
    (Fintype.equivFin σ).symm (Fintype.equivFin σ).symm.injective

omit hpA hpL hg hv in
/-- 有限全列挙の生成イデアルは、元の全同段δ関係の像のspan。 -/
theorem Andre.deltaDivisionFiniteJet_all_span [Fintype σ] :
    Ideal.span (Set.range fun i : Fin (Fintype.card σ) ↦ f₀ ((Fintype.equivFin σ).symm i)) =
      Ideal.span (Set.range f₀) := by
  congr 1
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨(Fintype.equivFin σ).symm i, rfl⟩
  · rintro ⟨s, rfl⟩
    refine ⟨Fintype.equivFin σ s, ?_⟩
    simp only [Equiv.symm_apply_apply]

end SerrePositivity.BhattScholze

end DeltaDivisionFiniteJetFamilyRegularity

/-! ## 元の有限δ関係の次段実商へのKoszul擬同型と射影分解 -/

@[expose] public noncomputable section DeltaDivisionFiniteJetStepResolution

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open _root_.CategoryTheory
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A)
variable (hpA : Function.Injective (fun z : A ↦ (p : A) * z))
variable (hpL : Function.Injective (fun z : RelativeFreeDeltaRing (R := A) σ ↦
  (p : RelativeFreeDeltaRing (R := A) σ) * z))
variable (hg : Function.Injective (WittVector.ghostMap :
  WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
variable (d : A) (a : σ → A) (v : Aˣ) (hv : (v : A) = D.delta d) (N : ℕ)
local notation "L₀" => RelativeFreeDeltaRing (R := A) σ
local notation "I₀" => Ideal.span {(p : L₀), MvPolynomial.C d} ⊔
  deltaDivisionFiniteRelationIdeal D d a (N + 1)
local notation "I₁" => Ideal.span {(p : L₀), MvPolynomial.C d} ⊔
  deltaDivisionFiniteRelationIdeal D d a (N + 2)
local notation "R₀" => L₀ ⧸ I₀
local notation "R₁" => L₀ ⧸ I₁
local notation "f₀" => fun s : σ ↦ Ideal.Quotient.mk I₀
  (deltaDivisionIteratedRelation D d a s (N + 2))

/-- 全同段関係の商内spanは、元の関係イデアルの標準商像。 -/
theorem Andre.deltaDivisionFiniteJetStep_span_eq_map :
    Ideal.span (Set.range f₀) =
      (Ideal.span (Set.range fun s ↦ _root_.SerrePositivity.BhattScholze.deltaDivisionIteratedRelation D d a s (N + 2))).map
        (Ideal.Quotient.mk I₀) := by
  rw [Ideal.map_span, ← Set.range_comp']

/-- 下位関係と全次段関係を合わせると、既存の次段の有限δ関係イデアルとなる。 -/
theorem Andre.deltaDivisionFiniteJetStep_sup_eq_next :
    I₀ ⊔ Ideal.span (Set.range fun s ↦ _root_.SerrePositivity.BhattScholze.deltaDivisionIteratedRelation D d a s (N + 2)) = I₁ := by
  rw [_root_.SerrePositivity.BhattScholze.deltaDivisionFiniteRelationIdeal_succ D d a (N + 1), ← sup_assoc]

/-- 元の下位δ関係商に全同段関係を課した二重商は、元の次段実商。 -/
def Andre.deltaDivisionFiniteJetStepQuotientEquiv : (R₀ ⧸ Ideal.span (Set.range f₀)) ≃+* R₁ :=
  (Ideal.quotEquivOfEq (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteJetStep_span_eq_map D d a N)).trans
    ((DoubleQuot.quotQuotEquivQuotSup I₀
      (Ideal.span (Set.range fun s ↦ _root_.SerrePositivity.BhattScholze.deltaDivisionIteratedRelation D d a s (N + 2)))).trans
      (Ideal.quotEquivOfEq (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteJetStep_sup_eq_next D d a N)))

/-- 二重商比較は元の自由環の標準商射と両立する。 -/
theorem Andre.deltaDivisionFiniteJetStepQuotientEquiv_mk (z : L₀) :
    _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteJetStepQuotientEquiv D d a N
      (Ideal.Quotient.mk _ (Ideal.Quotient.mk _ z)) = Ideal.Quotient.mk _ z := by
  rw [_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteJetStepQuotientEquiv, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
    RingEquiv.trans_apply]
  change (Ideal.quotEquivOfEq (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteJetStep_sup_eq_next D d a N))
    (DoubleQuot.quotQuotEquivQuotSup I₀
      (Ideal.span (Set.range fun s ↦ _root_.SerrePositivity.BhattScholze.deltaDivisionIteratedRelation D d a s (N + 2)))
      (DoubleQuot.quotQuotMk I₀
        (Ideal.span (Set.range fun s ↦ _root_.SerrePositivity.BhattScholze.deltaDivisionIteratedRelation D d a s (N + 2))) z)) = _
  rw [DoubleQuot.quotQuotEquivQuotSup_quotQuotMk, Ideal.quotEquivOfEq_mk]

/-- 元の下位δ関係商から次段実商への標準射。 -/
def Andre.deltaDivisionFiniteJetStepMap : R₀ →+* R₁ :=
  (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteJetStepQuotientEquiv D d a N).toRingHom.comp
    (Ideal.Quotient.mk (Ideal.span (Set.range f₀)))

/-- 次段標準射は元の自由環の商代表をそのまま送る。 -/
theorem Andre.deltaDivisionFiniteJetStepMap_mk (z : L₀) :
    _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteJetStepMap D d a N (Ideal.Quotient.mk _ z) = Ideal.Quotient.mk _ z :=
  _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteJetStepQuotientEquiv_mk D d a N z

/-- 次段実商の標準下位δ関係商代数構造。 -/
@[instance_reducible] def Andre.deltaDivisionFiniteJetStepAlgebra : Algebra R₀ R₁ :=
  (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteJetStepMap D d a N).toAlgebra

/-- 二重商比較は、標準下位商代数同型。 -/
def Andre.deltaDivisionFiniteJetStepQuotientAlgEquiv :
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteJetStepAlgebra D d a N
    (R₀ ⧸ Ideal.span (Set.range f₀)) ≃ₐ[R₀] R₁ := by
  letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteJetStepAlgebra D d a N
  apply AlgEquiv.ofRingEquiv (f := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteJetStepQuotientEquiv D d a N)
  intro c
  rfl

variable [Fintype σ]
local notation "g" => fun i : Fin (Fintype.card σ) ↦ f₀ (Equiv.symm (Fintype.equivFin σ) i)

/-- 有限全同段関係の実商は、元の次段δ関係商と標準下位商代数として同型。 -/
def Andre.deltaDivisionFiniteJetStepAllQuotientAlgEquiv :
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteJetStepAlgebra D d a N
    (R₀ ⧸ Ideal.span (Set.range g)) ≃ₐ[R₀] R₁ := by
  letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteJetStepAlgebra D d a N
  exact (Ideal.quotientEquivAlgOfEq R₀ (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteJet_all_span D d a N)).trans
    (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteJetStepQuotientAlgEquiv D d a N)

/-- 元の全同段Koszul複体の零次ホモロジーは、元の次段実商。 -/
def Andre.deltaDivisionFiniteJetStepHomologyZeroEquiv :
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteJetStepAlgebra D d a N
    (_root_.SerrePositivity.koszulComplex g).homology 0 ≃ₗ[R₀] R₁ := by
  letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteJetStepAlgebra D d a N
  exact (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteJet_all_isKoszulResolution D hpA hpL hg d a v hv N).equiv.some.trans
    (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteJetStepAllQuotientAlgEquiv D d a N).toLinearEquiv

/-- 元の全同段Koszul複体から次段実商の単一複体への具体的添加写像。 -/
def Andre.deltaDivisionFiniteJetStepAugmentation :
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteJetStepAlgebra D d a N
    _root_.SerrePositivity.koszulComplex g ⟶ (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
      (ModuleCat.of R₀ R₁) := by
  letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteJetStepAlgebra D d a N
  exact _root_.SerrePositivity.toSingleOfHomology _ _root_.SerrePositivity.koszulComplex_d_zero_one
    (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteJetStepHomologyZeroEquiv D hpA hpL hg d a v hv N).toModuleIso.hom

/-- 元の全同段Koszul添加写像は、元の次段実商への擬同型。 -/
theorem Andre.deltaDivisionFiniteJetStepAugmentation_quasiIso :
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteJetStepAlgebra D d a N
    QuasiIso (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteJetStepAugmentation D hpA hpL hg d a v hv N) := by
  let := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteJetStepAlgebra D d a N
  exact _root_.SerrePositivity.quasiIso_toSingleOfHomology _ _root_.SerrePositivity.koszulComplex_d_zero_one
    (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteJetStepHomologyZeroEquiv D hpA hpL hg d a v hv N).toModuleIso.hom
    (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteJet_all_isKoszulResolution D hpA hpL hg d a v hv N).isZero

/-- 元の全同段Koszul複体は、元の次段実δ関係商の共通APIによる射影分解。 -/
def Andre.deltaDivisionFiniteJetStepResolution :
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteJetStepAlgebra D d a N
    _root_.SerrePositivity.IsResolutionOf (_root_.SerrePositivity.koszulComplex g) (ModuleCat.of R₀ R₁) := by
  letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteJetStepAlgebra D d a N
  exact
    { isZero_X := _root_.SerrePositivity.koszulComplex_isZero_X_of_pos g
      projective := _root_.SerrePositivity.koszulComplex_projective_X g
      isZero_homology :=
        (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteJet_all_isKoszulResolution D hpA hpL hg d a v hv N).isZero
      homologyZeroIso :=
        (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteJetStepHomologyZeroEquiv D hpA hpL hg d a v hv N).toModuleIso }

end SerrePositivity.BhattScholze

end DeltaDivisionFiniteJetStepResolution

/-! ## 元のδ関係段間射と正規化段間射の標準比較

同じ初期N+2変数分離を両側へ使用し、後続変数を保つ係数変更を明示する。
-/

@[expose] public noncomputable section DeltaDivisionFiniteJetStepComparison

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A)
variable (hpA : Function.Injective (fun z : A ↦ (p : A) * z))
variable (hpL : Function.Injective (fun z : RelativeFreeDeltaRing (R := A) σ ↦
  (p : RelativeFreeDeltaRing (R := A) σ) * z))
variable (hg : Function.Injective (WittVector.ghostMap :
  WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
variable (d : A) (a : σ → A) (v : Aˣ) (hv : (v : A) = D.delta d) (N : ℕ)
local notation "L₀" => RelativeFreeDeltaRing (R := A) σ
local notation "I₀" => Ideal.span {(p : L₀), MvPolynomial.C d} ⊔
  deltaDivisionFiniteRelationIdeal D d a (N + 1)
local notation "I₁" => Ideal.span {(p : L₀), MvPolynomial.C d} ⊔
  deltaDivisionFiniteRelationIdeal D d a (N + 2)
local notation "J₁" => deltaDivisionFirstResidueIdeal D d a ⊔
  deltaDivisionFiniteNormalizedWittIdeal D d a v (N + 1)
local notation "K₁" => deltaDivisionFiniteNormalizedPresentationIdeal D d a v (N + 1)
local notation "S₀" => MvPolynomial (σ × Fin (N + 2)) A ⧸
  _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepSourceIdeal D d a v N
local notation "Q₁" => _root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionFiniteNormalizedQuotient D d a v (N + 1)

include hv in
/-- 全自由環の次段正規化イデアルは同じN+2変数分離で次段係数イデアルへ移る。 -/
theorem Andre.deltaDivisionNormalizedAmbientNextIdeal_map_split :
    Ideal.map (_root_.SerrePositivity.BhattScholze.relativeFreeFiniteVariableSplitAlgEquiv (N + 2) σ A).toRingHom J₁ =
      (K₁).map (MvPolynomial.C : MvPolynomial (σ × Fin (N + 2)) A →+*
        MvPolynomial (σ × ℕ) (MvPolynomial (σ × Fin (N + 2)) A)) := by
  rw [← _root_.SerrePositivity.BhattScholze.deltaDivisionFiniteNormalizedPresentationIdeal_map_initial D d a v hv (N + 1),
    Ideal.map_map]
  congr 1
  apply RingHom.ext
  intro f
  exact _root_.SerrePositivity.BhattScholze.relativeFreeFiniteVariableSplitAlgEquiv_initial (N + 2) σ A f

/-- 全自由環の次段正規化商は次段有限実商上の後続多項式環。 -/
def Andre.deltaDivisionNormalizedAmbientNextEquiv :
    (L₀ ⧸ J₁) ≃+* MvPolynomial (σ × ℕ) Q₁ :=
  (Ideal.quotientEquiv _ _ (_root_.SerrePositivity.BhattScholze.relativeFreeFiniteVariableSplitAlgEquiv (N + 2) σ A).toRingEquiv
    (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedAmbientNextIdeal_map_split D d a v hv N).symm).trans
    (MvPolynomial.quotientEquivQuotientMvPolynomial (σ := σ × ℕ) K₁).symm.toRingEquiv

/-- 次段正規化商の比較は、同じ変数分離後の標準係数商写像。 -/
theorem Andre.deltaDivisionNormalizedAmbientNextEquiv_mk (f : L₀) :
    _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedAmbientNextEquiv D d a v hv N (Ideal.Quotient.mk _ f) =
      MvPolynomial.map (Ideal.Quotient.mk K₁)
        (_root_.SerrePositivity.BhattScholze.relativeFreeFiniteVariableSplitAlgEquiv (N + 2) σ A f) := by
  rw [_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedAmbientNextEquiv, RingEquiv.trans_apply, Ideal.quotientEquiv_mk]
  change MvPolynomial.eval₂Hom (MvPolynomial.C.comp (Ideal.Quotient.mk K₁)) MvPolynomial.X
    (_root_.SerrePositivity.BhattScholze.relativeFreeFiniteVariableSplitAlgEquiv (N + 2) σ A f) =
    MvPolynomial.map (Ideal.Quotient.mk K₁)
      (_root_.SerrePositivity.BhattScholze.relativeFreeFiniteVariableSplitAlgEquiv (N + 2) σ A f)
  rw [MvPolynomial.map_eq_eval₂Hom_C_comp]

/-- 元の下位δ関係商を、有限実源商上の後続多項式環へ移す同型。 -/
def Andre.deltaDivisionFiniteJetStepSourceEquiv :
    (L₀ ⧸ I₀) ≃+* MvPolynomial (σ × ℕ) S₀ :=
  (_root_.SerrePositivity.BhattScholze.deltaDivisionFiniteNormalizedQuotientEquiv D hpA hpL hg d a v hv N).trans
    (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedAmbientSourceEquiv D d a v N hv)

/-- 元の下位商の比較は、逆Witt座標と標準係数商写像の合成。 -/
theorem Andre.deltaDivisionFiniteJetStepSourceEquiv_mk (f : L₀) :
    _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteJetStepSourceEquiv D hpA hpL hg d a v hv N (Ideal.Quotient.mk _ f) =
      MvPolynomial.map (Ideal.Quotient.mk (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepSourceIdeal D d a v N))
        (_root_.SerrePositivity.BhattScholze.relativeFreeFiniteVariableSplitAlgEquiv (N + 2) σ A
          (_root_.SerrePositivity.BhattScholze.relativeFreeWittInverseMap D hpA f)) := by
  rw [_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteJetStepSourceEquiv, RingEquiv.trans_apply,
    _root_.SerrePositivity.BhattScholze.deltaDivisionFiniteNormalizedQuotientEquiv_mk, _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedAmbientSourceEquiv_mk]

/-- 元の次段δ関係商を、次段有限実商上の後続多項式環へ移す同型。 -/
def Andre.deltaDivisionFiniteJetStepTargetEquiv :
    (L₀ ⧸ I₁) ≃+* MvPolynomial (σ × ℕ) Q₁ :=
  (_root_.SerrePositivity.BhattScholze.deltaDivisionFiniteNormalizedQuotientEquiv D hpA hpL hg d a v hv (N + 1)).trans
    (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedAmbientNextEquiv D d a v hv N)

/-- 元の次段商の比較も同じ逆座標・変数分離による標準係数商写像。 -/
theorem Andre.deltaDivisionFiniteJetStepTargetEquiv_mk (f : L₀) :
    _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteJetStepTargetEquiv D hpA hpL hg d a v hv N (Ideal.Quotient.mk _ f) =
      MvPolynomial.map (Ideal.Quotient.mk K₁)
        (_root_.SerrePositivity.BhattScholze.relativeFreeFiniteVariableSplitAlgEquiv (N + 2) σ A
          (_root_.SerrePositivity.BhattScholze.relativeFreeWittInverseMap D hpA f)) := by
  rw [_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteJetStepTargetEquiv, RingEquiv.trans_apply,
    _root_.SerrePositivity.BhattScholze.deltaDivisionFiniteNormalizedQuotientEquiv_mk, _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedAmbientNextEquiv_mk]

/-- 元の段間標準射は、正規化側標準射の後続多項式係数変更に一致する。 -/
theorem Andre.deltaDivisionFiniteJetStepComparison :
    (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteJetStepTargetEquiv D hpA hpL hg d a v hv N).toRingHom.comp
      (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteJetStepMap D d a N) =
    (MvPolynomial.map (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepNextMap D d a v N)).comp
      (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteJetStepSourceEquiv D hpA hpL hg d a v hv N).toRingHom := by
  apply Ideal.Quotient.ringHom_ext
  apply RingHom.ext
  intro f
  change _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteJetStepTargetEquiv D hpA hpL hg d a v hv N
    (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteJetStepMap D d a N (Ideal.Quotient.mk _ f)) =
    MvPolynomial.map (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepNextMap D d a v N)
      (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteJetStepSourceEquiv D hpA hpL hg d a v hv N (Ideal.Quotient.mk _ f))
  rw [_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteJetStepMap_mk, _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteJetStepTargetEquiv_mk,
    _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteJetStepSourceEquiv_mk, MvPolynomial.map_map]
  have hc : (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepNextMap D d a v N).comp
      (Ideal.Quotient.mk (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepSourceIdeal D d a v N)) =
      Ideal.Quotient.mk K₁ := by
    apply RingHom.ext
    intro z
    exact _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepNextMap_mk D d a v N z
  rw [hc]

end SerrePositivity.BhattScholze

end DeltaDivisionFiniteJetStepComparison

/-! ## 元のδ段間射の標準係数射・スカラー塔と係数環上の平坦性 -/

@[expose] public noncomputable section DeltaDivisionFiniteJetStepScalarTower

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A)
variable (hpA : Function.Injective (fun z : A ↦ (p : A) * z))
variable (hpL : Function.Injective (fun z : RelativeFreeDeltaRing (R := A) σ ↦
  (p : RelativeFreeDeltaRing (R := A) σ) * z))
variable (hg : Function.Injective (WittVector.ghostMap :
  WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
variable (d : A) (a : σ → A) (v : Aˣ) (hv : (v : A) = D.delta d) (N : ℕ)
local notation "L₀" => RelativeFreeDeltaRing (R := A) σ
local notation "R₀" => L₀ ⧸ (Ideal.span {(p : L₀), MvPolynomial.C d} ⊔
  deltaDivisionFiniteRelationIdeal D d a (N + 1))
local notation "R₁" => L₀ ⧸ (Ideal.span {(p : L₀), MvPolynomial.C d} ⊔
  deltaDivisionFiniteRelationIdeal D d a (N + 2))
local notation "Q₀" => _root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionFiniteNormalizedQuotient D d a v N
local notation "Q₁" => _root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionFiniteNormalizedQuotient D d a v (N + 1)
local notation "S₀" => MvPolynomial (σ × Fin (N + 2)) A ⧸
  _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepSourceIdeal D d a v N

/-- 前段正規化商から元の下位δ関係商への標準係数射。 -/
def Andre.deltaDivisionFiniteJetSourceCoefficientMap : Q₀ →+* R₀ :=
  (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteJetStepSourceEquiv D hpA hpL hg d a v hv N).symm.toRingHom.comp
    ((MvPolynomial.C : S₀ →+* MvPolynomial (σ × ℕ) S₀).comp
      (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepSourceCoefficientMap D d a v N))

/-- 前段正規化商から元の次段δ関係商への標準係数射。 -/
def Andre.deltaDivisionFiniteJetTargetCoefficientMap : Q₀ →+* R₁ :=
  (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteJetStepTargetEquiv D hpA hpL hg d a v hv N).symm.toRingHom.comp
    ((MvPolynomial.C : Q₁ →+* MvPolynomial (σ × ℕ) Q₁).comp
      (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedStepMap D d a v N))

/-- 元の段間射と標準係数射の合成は、次段商の標準係数射。 -/
theorem Andre.deltaDivisionFiniteJetStepMap_comp_coefficient :
    (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteJetStepMap D d a N).comp
      (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteJetSourceCoefficientMap D hpA hpL hg d a v hv N) =
      _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteJetTargetCoefficientMap D hpA hpL hg d a v hv N := by
  apply RingHom.ext
  intro c
  let eS := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteJetStepSourceEquiv D hpA hpL hg d a v hv N
  let eT := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteJetStepTargetEquiv D hpA hpL hg d a v hv N
  apply eT.injective
  change eT (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteJetStepMap D d a N
      (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteJetSourceCoefficientMap D hpA hpL hg d a v hv N c)) =
    eT (eT.symm (MvPolynomial.C (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedStepMap D d a v N c)))
  rw [RingEquiv.apply_symm_apply]
  have h := RingHom.congr_fun
    (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteJetStepComparison D hpA hpL hg d a v hv N)
    (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteJetSourceCoefficientMap D hpA hpL hg d a v hv N c)
  change eT (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteJetStepMap D d a N
      (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteJetSourceCoefficientMap D hpA hpL hg d a v hv N c)) =
    MvPolynomial.map (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepNextMap D d a v N)
      (eS (eS.symm
        (MvPolynomial.C (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepSourceCoefficientMap D d a v N c)))) at h
  rw [RingEquiv.apply_symm_apply, MvPolynomial.map_C] at h
  exact h.trans (congrArg MvPolynomial.C
    (RingHom.congr_fun (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepNextMap_comp_coefficient D d a v N) c))

/-- 元の下位δ関係商の標準前段正規化商代数構造。 -/
@[instance_reducible] def Andre.deltaDivisionFiniteJetSourceAlgebra : Algebra Q₀ R₀ :=
  (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteJetSourceCoefficientMap D hpA hpL hg d a v hv N).toAlgebra

/-- 元の次段δ関係商の標準前段正規化商代数構造。 -/
@[instance_reducible] def Andre.deltaDivisionFiniteJetTargetAlgebra : Algebra Q₀ R₁ :=
  (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteJetTargetCoefficientMap D hpA hpL hg d a v hv N).toAlgebra

/-- 元の下位商の比較は、標準前段正規化商代数同型。 -/
def Andre.deltaDivisionFiniteJetSourceAlgEquiv :
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepSourceAlgebra D d a v N
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteJetSourceAlgebra D hpA hpL hg d a v hv N
    R₀ ≃ₐ[Q₀] MvPolynomial (σ × ℕ) S₀ := by
  letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepSourceAlgebra D d a v N
  letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteJetSourceAlgebra D hpA hpL hg d a v hv N
  apply AlgEquiv.ofRingEquiv (f := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteJetStepSourceEquiv D hpA hpL hg d a v hv N)
  intro c
  exact (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteJetStepSourceEquiv D hpA hpL hg d a v hv N).apply_symm_apply _

/-- 元の次段商の比較も、標準前段正規化商代数同型。 -/
def Andre.deltaDivisionFiniteJetTargetAlgEquiv :
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedStepAlgebra D d a v N
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteJetTargetAlgebra D hpA hpL hg d a v hv N
    R₁ ≃ₐ[Q₀] MvPolynomial (σ × ℕ) Q₁ := by
  letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedStepAlgebra D d a v N
  letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteJetTargetAlgebra D hpA hpL hg d a v hv N
  apply AlgEquiv.ofRingEquiv (f := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteJetStepTargetEquiv D hpA hpL hg d a v hv N)
  intro c
  exact (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteJetStepTargetEquiv D hpA hpL hg d a v hv N).apply_symm_apply _

/-- 元の下位商は標準前段正規化商射により自由。 -/
theorem Andre.deltaDivisionFiniteJetSource_moduleFree :
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteJetSourceAlgebra D hpA hpL hg d a v hv N
    Module.Free Q₀ R₀ := by
  let := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepSourceAlgebra D d a v N
  let := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteJetSourceAlgebra D hpA hpL hg d a v hv N
  let := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionNormalizedStepSource_moduleFree D d a v N
  let : Module.Free Q₀ (MvPolynomial (σ × ℕ) S₀) :=
    Module.Free.of_equiv ((MvPolynomial.basisMonomials (σ × ℕ) S₀).repr.restrictScalars Q₀).symm
  exact Module.Free.of_equiv
    (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteJetSourceAlgEquiv D hpA hpL hg d a v hv N).symm.toLinearEquiv

/-- 元の次段商も標準前段正規化商射により自由。 -/
theorem Andre.deltaDivisionFiniteJetTarget_moduleFree :
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteJetTargetAlgebra D hpA hpL hg d a v hv N
    Module.Free Q₀ R₁ := by
  let := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedStepAlgebra D d a v N
  let := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteJetTargetAlgebra D hpA hpL hg d a v hv N
  let := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteNormalizedStep_moduleFree D d a v N
  let : Module.Free Q₀ (MvPolynomial (σ × ℕ) Q₁) :=
    Module.Free.of_equiv ((MvPolynomial.basisMonomials (σ × ℕ) Q₁).repr.restrictScalars Q₀).symm
  exact Module.Free.of_equiv
    (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteJetTargetAlgEquiv D hpA hpL hg d a v hv N).symm.toLinearEquiv

/-- 元の下位商は標準係数射で前段正規化商上平坦。 -/
theorem Andre.deltaDivisionFiniteJetSource_moduleFlat :
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteJetSourceAlgebra D hpA hpL hg d a v hv N
    Module.Flat Q₀ R₀ := by
  let := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteJetSourceAlgebra D hpA hpL hg d a v hv N
  let := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteJetSource_moduleFree D hpA hpL hg d a v hv N
  infer_instance

/-- 元の次段商も標準係数射で前段正規化商上平坦。 -/
theorem Andre.deltaDivisionFiniteJetTarget_moduleFlat :
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteJetTargetAlgebra D hpA hpL hg d a v hv N
    Module.Flat Q₀ R₁ := by
  let := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteJetTargetAlgebra D hpA hpL hg d a v hv N
  let := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteJetTarget_moduleFree D hpA hpL hg d a v hv N
  infer_instance

/-- 前段正規化商・元の下位商・元の次段商の標準スカラー塔。 -/
theorem Andre.deltaDivisionFiniteJetStep_isScalarTower :
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteJetSourceAlgebra D hpA hpL hg d a v hv N
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteJetTargetAlgebra D hpA hpL hg d a v hv N
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteJetStepAlgebra D d a N
    IsScalarTower Q₀ R₀ R₁ := by
  let := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteJetSourceAlgebra D hpA hpL hg d a v hv N
  let := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteJetTargetAlgebra D hpA hpL hg d a v hv N
  let := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteJetStepAlgebra D d a N
  exact IsScalarTower.of_algebraMap_eq'
    (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteJetStepMap_comp_coefficient D hpA hpL hg d a v hv N).symm

end SerrePositivity.BhattScholze

end DeltaDivisionFiniteJetStepScalarTower

/-! ## 元のδ段間射の係数拡大加群に対する実Tor・Koszul計算 -/

@[expose] public noncomputable section DeltaDivisionFiniteJetStepTor

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open _root_.CategoryTheory _root_.CategoryTheory.Limits
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A)
variable (hpA : Function.Injective (fun z : A ↦ (p : A) * z))
variable (hpL : Function.Injective (fun z : RelativeFreeDeltaRing (R := A) σ ↦
  (p : RelativeFreeDeltaRing (R := A) σ) * z))
variable (hg : Function.Injective (WittVector.ghostMap :
  WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
variable (d : A) (a : σ → A) (v : Aˣ) (hv : (v : A) = D.delta d) (N : ℕ)
local notation "L₀" => RelativeFreeDeltaRing (R := A) σ
local notation "I₀" => Ideal.span {(p : L₀), MvPolynomial.C d} ⊔
  deltaDivisionFiniteRelationIdeal D d a (N + 1)
local notation "R₀" => L₀ ⧸ I₀
local notation "R₁" => L₀ ⧸ (Ideal.span {(p : L₀), MvPolynomial.C d} ⊔
  deltaDivisionFiniteRelationIdeal D d a (N + 2))
local notation "Q₀" => _root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionFiniteNormalizedQuotient D d a v N

/-- 任意前段正規化商加群の係数拡大に対し、元の段間射の高次Torは零。 -/
theorem Andre.deltaDivisionFiniteJetStep_tor_subsingleton
    (M : Type u) [AddCommGroup M] [Module Q₀ M] (i : ℕ) :
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteJetSourceAlgebra D hpA hpL hg d a v hv N
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteJetTargetAlgebra D hpA hpL hg d a v hv N
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteJetStepAlgebra D d a N
    Subsingleton (_root_.SerrePositivity.TorModule R₀ (i + 1) R₁ (TensorProduct Q₀ R₀ M)) := by
  let := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteJetSourceAlgebra D hpA hpL hg d a v hv N
  let := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteJetTargetAlgebra D hpA hpL hg d a v hv N
  let := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteJetStepAlgebra D d a N
  let := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteJetSource_moduleFlat D hpA hpL hg d a v hv N
  let := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteJetTarget_moduleFlat D hpA hpL hg d a v hv N
  let := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteJetStep_isScalarTower D hpA hpL hg d a v hv N
  exact _root_.SerrePositivity.torModule_baseChange_subsingleton Q₀ R₀ R₁ M (i + 1)
    (_root_.SerrePositivity.torModule_subsingleton_of_flat R₁ M i)

/-- 同じ元の実導来テンソルは次数零に集中する。添字集合の有限性は不要。 -/
theorem Andre.deltaDivisionFiniteJetStep_derivedTensor_concentrated
    (M : Type u) [AddCommGroup M] [Module Q₀ M] :
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteJetSourceAlgebra D hpA hpL hg d a v hv N
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteJetTargetAlgebra D hpA hpL hg d a v hv N
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteJetStepAlgebra D d a N
    _root_.SerrePositivity.IsConcentratedInDegreeZero (_root_.SerrePositivity.derivedTensor R₀ R₁ (TensorProduct Q₀ R₀ M)) := by
  let := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteJetSourceAlgebra D hpA hpL hg d a v hv N
  let := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteJetTargetAlgebra D hpA hpL hg d a v hv N
  let := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteJetStepAlgebra D d a N
  rw [_root_.SerrePositivity.isConcentratedInDegreeZero_derivedTensor_iff]
  intro i hi
  cases i with
  | zero => exact (Nat.lt_irrefl 0 hi).elim
  | succ i => exact _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteJetStep_tor_subsingleton D hpA hpL hg d a v hv N M i

variable [Fintype σ]
local notation "g" => fun i : Fin (Fintype.card σ) ↦ Ideal.Quotient.mk I₀
  (deltaDivisionIteratedRelation D d a (Equiv.symm (Fintype.equivFin σ) i) (N + 2))

/-- 元の有限δ関係の実Koszulホモロジーと実次段商のTorとの比較。 -/
def Andre.deltaDivisionFiniteJetStepKoszulTorIso
    (M : Type u) [AddCommGroup M] [Module Q₀ M] (i : ℕ) :
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteJetSourceAlgebra D hpA hpL hg d a v hv N
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteJetTargetAlgebra D hpA hpL hg d a v hv N
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteJetStepAlgebra D d a N
    ModuleCat.of R₀ (_root_.SerrePositivity.TorModule R₀ i R₁ (TensorProduct Q₀ R₀ M)) ≅
      ((_root_.SerrePositivity.koszulModuleFunctor g).obj
        (ModuleCat.of R₀ (TensorProduct Q₀ R₀ M))).homology (-(i : ℤ)) := by
  letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteJetSourceAlgebra D hpA hpL hg d a v hv N
  letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteJetTargetAlgebra D hpA hpL hg d a v hv N
  letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteJetStepAlgebra D d a N
  exact _root_.SerrePositivity.torModuleIsoCochainLeft (TensorProduct Q₀ R₀ M)
    (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteJetStepResolution D hpA hpL hg d a v hv N) i ≪≫
    (HomologicalComplex.homologyFunctor _ _ (-(i : ℤ))).mapIso
      (_root_.SerrePositivity.koszulTensorConeIso g (ModuleCat.of R₀ (TensorProduct Q₀ R₀ M)))

/-- 任意係数加群の拡大上で元の全同段δ関係の負次Koszulホモロジーは零。 -/
theorem Andre.deltaDivisionFiniteJetStepKoszulHomology_isZero
    (M : Type u) [AddCommGroup M] [Module Q₀ M] (i : ℕ) :
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteJetSourceAlgebra D hpA hpL hg d a v hv N
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteJetTargetAlgebra D hpA hpL hg d a v hv N
    letI := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteJetStepAlgebra D d a N
    IsZero (((_root_.SerrePositivity.koszulModuleFunctor g).obj
      (ModuleCat.of R₀ (TensorProduct Q₀ R₀ M))).homology (-((i + 1 : ℕ) : ℤ))) := by
  let := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteJetSourceAlgebra D hpA hpL hg d a v hv N
  let := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteJetTargetAlgebra D hpA hpL hg d a v hv N
  let := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteJetStepAlgebra D d a N
  let := _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteJetStep_tor_subsingleton D hpA hpL hg d a v hv N M i
  exact IsZero.of_iso (ModuleCat.isZero_of_subsingleton _)
    (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteJetStepKoszulTorIso D hpA hpL hg d a v hv N M (i + 1)).symm

end SerrePositivity.BhattScholze

end DeltaDivisionFiniteJetStepTor
