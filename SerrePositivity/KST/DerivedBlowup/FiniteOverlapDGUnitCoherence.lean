module

public import SerrePositivity.KST.DerivedBlowup.FiniteOverlapRestrictionComparison
public import SerrePositivity.KST.DerivedBlowup.FiniteOverlapDGIdentity

/-!
概要：KST §3.1 の有限重なりの制限合成比較の左右の単位整合性。
方針：恒等射が含まれる合成比較を、標準恒等制限比較と各 Hom の成分で比較する。
規約：有限集合の恒等包含の合成は証明の無関係性で同定する。
使われ方：有限チャート dg 図式の単位の高次整合性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory
open DifferentialGraded DifferentialGraded.ScalarExtension

variable (R : Type u) [CommRing R] {I : Type} [DecidableEq I]

set_option synthInstance.maxHeartbeats 100000 in
-- 局所化環の複体のモノイダル構造を照合するために必要。
/-- 概要：外側の恒等重なり制限を解消する標準 dg 比較。
方針：恒等環射への等式移送の後に恒等制限比較を適用する。
規約：KST §3.1。使われ方：制限合成比較の左単位整合性。 -/
def finiteOverlapDGLeftIdentityComparison (a : I → R) (i k : I) {T U : Finset I}
    (h : T ⊆ U) (hi : i ∈ T) :
    DGFunctor (FiniteOverlapRing R i T)
      (DGRestriction (finiteOverlapChartMap R i i (Finset.Subset.refl T) hi).toRingHom
        (DGRestriction (finiteOverlapChartMap R i k h hi).toRingHom
          (FiniteOverlapKoszulObject R a k U)))
      (DGRestriction (finiteOverlapChartMap R i k h hi).toRingHom
        (FiniteOverlapKoszulObject R a k U)) :=
  EnrichedFunctor.comp (Complex (FiniteOverlapRing R i T))
    (restrictionRingHomTransportDGFunctor (finiteOverlapChartMap_ringHom_refl R i T hi)
      (DGRestriction (finiteOverlapChartMap R i k h hi).toRingHom
        (FiniteOverlapKoszulObject R a k U)))
    (restrictionIdentityDGFunctor (FiniteOverlapRing R i T)
      (DGRestriction (finiteOverlapChartMap R i k h hi).toRingHom
        (FiniteOverlapKoszulObject R a k U)))

set_option maxHeartbeats 2000000 in
-- 局所化環の恒等制限と内側の係数制限の成分を照合するために必要。
set_option synthInstance.maxHeartbeats 100000 in
-- 局所化環の複体のモノイダル構造を照合するために必要。
/-- 概要：外側の恒等制限比較は Hom の元を変えない。
方針：恒等制限比較を計算し、環射等式移送の成分公式を使う。
規約：KST §3.1。使われ方：左単位整合性の各次数の計算。 -/
theorem finiteOverlapDGLeftIdentityComparison_apply (a : I → R) (i k : I) {T U : Finset I}
    (h : T ⊆ U) (hi : i ∈ T) (v w : FiniteOverlapKoszulObject R a k U) (q : ℤ)
    (z : (homObject (FiniteOverlapRing R k U) (FiniteOverlapKoszulObject R a k U) v w).X q) :
    (((finiteOverlapDGLeftIdentityComparison R a i k h hi).map v w).f q) z = z := by
  change (((restrictionRingHomTransportDGFunctor (finiteOverlapChartMap_ringHom_refl R i T hi)
    (DGRestriction (finiteOverlapChartMap R i k h hi).toRingHom
      (FiniteOverlapKoszulObject R a k U))).map v w).f q) z = z
  exact restrictionRingHomTransportDGFunctor_restrictedExterior_apply _ _ _ v w q z

set_option maxHeartbeats 4000000 in
-- 局所化環の合成制限と恒等制限の標準比較を照合するために必要。
set_option synthInstance.maxHeartbeats 100000 in
-- 局所化環の複体のモノイダル構造を照合するために必要。
/-- 概要：恒等包含を外側に持つ合成比較は左恒等制限比較と一致する。
方針：一対象型の対象を比較し、Hom の各次数で両比較の恒等性を使う。
規約：KST §3.1。使われ方：全有限チャート dg 図式の左単位整合性。 -/
theorem finiteOverlapDGCompositionComparison_left_unit (a : I → R) (i k : I)
    {T U : Finset I} (h : T ⊆ U) (hi : i ∈ T) :
    finiteOverlapDGCompositionComparison R a i i k (Finset.Subset.refl T) h hi hi =
      finiteOverlapDGLeftIdentityComparison R a i k h hi := by
  have hsingle : Subsingleton (FiniteOverlapKoszulObject R a k U) :=
    ⟨fun x y => by cases x; cases y; rfl⟩
  refine EnrichedFunctor.ext (Complex (FiniteOverlapRing R i T))
    (F := finiteOverlapDGCompositionComparison R a i i k (Finset.Subset.refl T) h hi hi)
    (G := finiteOverlapDGLeftIdentityComparison R a i k h hi) (fun _ => hsingle.elim _ _) ?_
  intro v w
  simp only [eqToHom_refl, Category.comp_id]
  apply HomologicalComplex.Hom.ext
  funext q
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  change (((finiteOverlapDGCompositionComparison R a i i k
      (Finset.Subset.refl T) h hi hi).map v w).f q) z =
    (((finiteOverlapDGLeftIdentityComparison R a i k h hi).map v w).f q) z
  rw [finiteOverlapDGCompositionComparison_apply, finiteOverlapDGLeftIdentityComparison_apply]

set_option maxHeartbeats 4000000 in
-- 局所化環の合成制限と係数制限した恒等比較を照合するために必要。
set_option synthInstance.maxHeartbeats 100000 in
-- 局所化環の複体のモノイダル構造を照合するために必要。
/-- 概要：恒等包含を内側に持つ合成比較は係数制限した恒等比較と一致する。
方針：一対象型の対象を比較し、Hom の各次数で両比較の恒等性を使う。
規約：KST §3.1。使われ方：全有限チャート dg 図式の右単位整合性。 -/
theorem finiteOverlapDGCompositionComparison_right_unit (a : I → R) (i k : I)
    {T U : Finset I} (h : T ⊆ U) (hi : i ∈ T) (hk : k ∈ U) :
    finiteOverlapDGCompositionComparison R a i k k h (Finset.Subset.refl U) hi hk =
      restrictDGFunctor (finiteOverlapChartMap R i k h hi).toRingHom
        (finiteOverlapDGIdentityComparison R a k U hk) := by
  have hsingle : Subsingleton (FiniteOverlapKoszulObject R a k U) :=
    ⟨fun x y => by cases x; cases y; rfl⟩
  refine EnrichedFunctor.ext (Complex (FiniteOverlapRing R i T))
    (F := finiteOverlapDGCompositionComparison R a i k k h (Finset.Subset.refl U) hi hk)
    (G := restrictDGFunctor (finiteOverlapChartMap R i k h hi).toRingHom
      (finiteOverlapDGIdentityComparison R a k U hk)) (fun _ => hsingle.elim _ _) ?_
  intro v w
  simp only [eqToHom_refl, Category.comp_id]
  apply HomologicalComplex.Hom.ext
  funext q
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  change (((finiteOverlapDGCompositionComparison R a i k k h
      (Finset.Subset.refl U) hi hk).map v w).f q) z =
    (((finiteOverlapDGIdentityComparison R a k U hk).map v w).f q) z
  rw [finiteOverlapDGCompositionComparison_apply, finiteOverlapDGIdentityComparison_apply]

end SerrePositivity.KST.DerivedBlowup
