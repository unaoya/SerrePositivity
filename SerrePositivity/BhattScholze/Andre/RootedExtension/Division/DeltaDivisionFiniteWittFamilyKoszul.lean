module

public import SerrePositivity.BhattScholze.Andre.RootedExtension.Division.DeltaDivisionFiniteJetRegularity
public import Mathlib.RingTheory.Regular.Flat

/-! # 任意有限根族の次段Witt関係の実残余Koszul分解 -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (d : A) (a : σ → A) (v : Aˣ) (N : ℕ)
local notation "L₀" => RelativeFreeDeltaRing (R := A) σ
local notation "J" => deltaDivisionFirstResidueIdeal D d a ⊔
  deltaDivisionFiniteNormalizedWittIdeal D d a v N
local notation "S₀" => MvPolynomial (σ × Fin (N + 2)) A ⧸
  deltaDivisionNormalizedStepSourceIdeal D d a v N
local notation "I₀" => Ideal.span {(p : L₀), MvPolynomial.C d} ⊔
  deltaDivisionFiniteRelationIdeal D d a (N + 1)

/-- 後続変数を残す実正規化商でも、異なる有限個の次段関係は弱正則。 -/
theorem deltaDivisionNormalizedAmbientSource_fin_isWeaklyRegular
    (hv : (v : A) = D.delta d) {m : ℕ} (s : Fin m → σ)
    (hs : Function.Injective s) :
    RingTheory.Sequence.IsWeaklyRegular (L₀ ⧸ J)
      (List.ofFn fun i => Ideal.Quotient.mk J
        (relativeFreeFiniteInitialPolynomialMap (N + 2) σ A
          (deltaDivisionWittNormalizedPolynomial D d a v (s i) N))) := by
  let e := deltaDivisionNormalizedAmbientSourceEquiv D d a v N hv
  let rs := List.ofFn fun i => Ideal.Quotient.mk J
    (relativeFreeFiniteInitialPolynomialMap (N + 2) σ A
      (deltaDivisionWittNormalizedPolynomial D d a v (s i) N))
  have hr := (deltaDivisionNormalizedStepSourceRelation_fin_isWeaklyRegular
    D d a v N s hs).of_flat (S := MvPolynomial (σ × ℕ) S₀)
  refine (e.toAddEquiv.isWeaklyRegular_congr (as := rs) (bs := rs.map e) ?_).mpr ?_
  · apply List.forall₂_map_right_iff.mpr
    apply List.forall₂_same.mpr
    intro r _ x
    exact e.map_mul r x
  · simpa only [rs, List.map_ofFn, Function.comp_def, e,
      deltaDivisionNormalizedAmbientSourceEquiv_initial, MvPolynomial.algebraMap_eq] using hr

/-- 同じ実正規化商で、次段Witt有限族のKoszul複体は通常商を分解する。 -/
theorem deltaDivisionNormalizedAmbientSource_fin_isKoszulResolution
    (hv : (v : A) = D.delta d) {m : ℕ} (s : Fin m → σ)
    (hs : Function.Injective s) :
    SerrePositivity.IsKoszulResolution (fun i => Ideal.Quotient.mk J
      (relativeFreeFiniteInitialPolynomialMap (N + 2) σ A
        (deltaDivisionWittNormalizedPolynomial D d a v (s i) N))) :=
  SerrePositivity.isKoszulResolution_of_isWeaklyRegular _
    (deltaDivisionNormalizedAmbientSource_fin_isWeaklyRegular D d a v N hv s hs)

variable (hpA : Function.Injective (fun z : A => (p : A) * z))
variable (hpL : Function.Injective (fun z : RelativeFreeDeltaRing (R := A) σ =>
  (p : RelativeFreeDeltaRing (R := A) σ) * z))
variable (hg : Function.Injective (WittVector.ghostMap :
  WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ →
    RelativeFreeDeltaRing (R := A) σ))
include hpA hpL hg

/-- 元の自由δ環の実下位関係商でも、次段Witt有限族は弱正則。 -/
theorem deltaDivisionFiniteWittRelation_quotient_fin_isWeaklyRegular
    (hv : (v : A) = D.delta d) {m : ℕ} (s : Fin m → σ)
    (hs : Function.Injective s) :
    RingTheory.Sequence.IsWeaklyRegular (L₀ ⧸ I₀)
      (List.ofFn fun i => Ideal.Quotient.mk I₀
        (deltaDivisionRelativeWittRelationElement D d a v (s i) N)) := by
  let e := deltaDivisionFiniteNormalizedQuotientEquiv D hpA hpL hg d a v hv N
  let rs := List.ofFn fun i => Ideal.Quotient.mk I₀
    (deltaDivisionRelativeWittRelationElement D d a v (s i) N)
  have he (t : σ) : e (Ideal.Quotient.mk I₀
      (deltaDivisionRelativeWittRelationElement D d a v t N)) =
      Ideal.Quotient.mk J (relativeFreeFiniteInitialPolynomialMap (N + 2) σ A
        (deltaDivisionWittNormalizedPolynomial D d a v t N)) := by
    dsimp only [e]
    rw [deltaDivisionFiniteNormalizedQuotientEquiv_mk,
      deltaDivisionRelativeWittRelationElement_inverse_image D hpA hg]
  refine (e.toAddEquiv.isWeaklyRegular_congr (as := rs) (bs := rs.map e) ?_).mpr ?_
  · apply List.forall₂_map_right_iff.mpr
    apply List.forall₂_same.mpr
    intro r _ x
    exact e.map_mul r x
  · simpa only [rs, List.map_ofFn, Function.comp_def, he] using
      deltaDivisionNormalizedAmbientSource_fin_isWeaklyRegular D d a v N hv s hs

/-- 元の実商上の次段Witt有限族は、実通常商のKoszul分解を与える。 -/
theorem deltaDivisionFiniteWittRelation_quotient_fin_isKoszulResolution
    (hv : (v : A) = D.delta d) {m : ℕ} (s : Fin m → σ)
    (hs : Function.Injective s) :
    SerrePositivity.IsKoszulResolution (fun i => Ideal.Quotient.mk I₀
      (deltaDivisionRelativeWittRelationElement D d a v (s i) N)) :=
  SerrePositivity.isKoszulResolution_of_isWeaklyRegular _
    (deltaDivisionFiniteWittRelation_quotient_fin_isWeaklyRegular
      D d a v N hpA hpL hg hv s hs)

end SerrePositivity.BhattScholze
