module

public import SerrePositivity.KST.DerivedBlowup.FiniteOverlapDGComposition

/-!
概要：KST §3.1 の有限重なりの制限合成比較を任意の dg 圏で使える形にする。
方針：チャート模型に限定しない標準比較を束ね、外積模型とその係数制限上で成分を計算する。
規約：係数環射は既存の有限重なり関手のものを使う。
使われ方：三段階以上の有限重なりの制限比較の結合整合性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory
open DifferentialGraded DifferentialGraded.ScalarExtension

variable (R : Type u) [CommRing R] {I : Type} [DecidableEq I]

set_option synthInstance.maxHeartbeats 100000 in
-- 局所化係数環の複体のモノイダル構造を照合するために必要。
/-- 概要：任意の dg 圏での有限重なりの係数制限の合成比較。
方針：標準制限合成比較と環図式の合成等式による移送を合成する。
規約：KST §3.1。使われ方：高次の制限比較を二経路で構成する。 -/
def finiteOverlapRestrictionCompositionComparison (i k l : I) {T U V : Finset I}
    (h : T ⊆ U) (g : U ⊆ V) (hi : i ∈ T) (hk : k ∈ U)
    (D : Type v) [DGCategory (FiniteOverlapRing R l V) D] :
    DGFunctor (FiniteOverlapRing R i T)
      (DGRestriction (finiteOverlapChartMap R i k h hi).toRingHom
        (DGRestriction (finiteOverlapChartMap R k l g hk).toRingHom D))
      (DGRestriction (finiteOverlapChartMap R i l (h.trans g) hi).toRingHom D) :=
  EnrichedFunctor.comp (Complex (FiniteOverlapRing R i T))
    (restrictionCompositionDGFunctor (finiteOverlapChartMap R i k h hi).toRingHom
      (finiteOverlapChartMap R k l g hk).toRingHom D)
    (restrictionRingHomTransportDGFunctor (finiteOverlapChartMap_ringHom_comp R i k l h g hi hk) D)

set_option maxHeartbeats 1000000 in
-- 局所化環上の制限合成比較の対象写像を照合するために必要。
set_option synthInstance.maxHeartbeats 100000 in
-- 局所化係数環の複体のモノイダル構造を照合するために必要。
/-- 概要：一般化した制限合成比較は対象を保つ。
方針：環射等式による比較の対象公式を使う。
規約：KST §3.1。使われ方：結合整合性の対象写像の照合。 -/
theorem finiteOverlapRestrictionCompositionComparison_obj (i k l : I) {T U V : Finset I}
    (h : T ⊆ U) (g : U ⊆ V) (hi : i ∈ T) (hk : k ∈ U)
    (D : Type v) [DGCategory (FiniteOverlapRing R l V) D] (x : D) :
    (finiteOverlapRestrictionCompositionComparison R i k l h g hi hk D).obj x = x :=
  restrictionRingHomTransportDGFunctor_obj _ D x

variable {A B C M : Type u} [CommRing A] [CommRing B] [CommRing C]
  [AddCommGroup M] [Module C M]

/-- 概要：制限済み外積模型でも環射等式による比較は各次数の元を変えない。
方針：環射等式を消去して恒等 dg 関手の成分を計算する。
規約：KST §3.1。使われ方：三段階の制限比較の内側の Hom 計算。 -/
theorem restrictionRingHomTransportDGFunctor_restrictedExterior_apply
    {φ ψ : A →+* B} (h : φ = ψ) (χ : B →+* C) (d : M →ₗ[C] C)
    (x y : ExteriorKoszulObject d) (q : ℤ) (z : (exteriorKoszulCochain d).X q) :
    (((restrictionRingHomTransportDGFunctor h
      (DGRestriction χ (ExteriorKoszulObject d))).map x y).f q)
      z = z := by
  cases h
  rfl

variable {E N : Type u} [CommRing E] [AddCommGroup N] [Module E N]

set_option maxHeartbeats 1000000 in
-- 局所化環上の三段階の係数制限の各成分を照合するために必要。
set_option synthInstance.maxHeartbeats 100000 in
-- 局所化係数環の複体のモノイダル構造を照合するために必要。
/-- 概要：外積模型の係数制限上の合成比較は各次数の元を変えない。
方針：制限合成比較と環射等式による比較の各成分を計算する。
規約：KST §3.1。使われ方：結合整合性の Hom 写像の照合。 -/
theorem finiteOverlapRestrictionCompositionComparison_restricted_apply
    (i k l : I) {T U V : Finset I} (h : T ⊆ U) (g : U ⊆ V) (hi : i ∈ T) (hk : k ∈ U)
    (χ : FiniteOverlapRing R l V →+* E) (d : N →ₗ[E] E)
    (x y : ExteriorKoszulObject d) (q : ℤ) (z : (exteriorKoszulCochain d).X q) :
    (((finiteOverlapRestrictionCompositionComparison R i k l h g hi hk
      (DGRestriction χ (ExteriorKoszulObject d))).map x y).f q) z = z := by
  change (((restrictionRingHomTransportDGFunctor
    (finiteOverlapChartMap_ringHom_comp R i k l h g hi hk)
    (DGRestriction χ (ExteriorKoszulObject d))).map x y).f q) z = z
  exact restrictionRingHomTransportDGFunctor_restrictedExterior_apply _ χ d x y q z

set_option maxHeartbeats 1000000 in
-- 局所化環上の二段階の係数制限の各成分を照合するために必要。
set_option synthInstance.maxHeartbeats 100000 in
-- 局所化係数環の複体のモノイダル構造を照合するために必要。
/-- 概要：一般化した比較は既存の有限重なりチャート比較に一致する。
方針：両定義が同じ標準比較の合成であることを確認する。
規約：KST §3.1。使われ方：既存の恒等・合成律と高次比較を接続する。 -/
theorem finiteOverlapRestrictionCompositionComparison_chart (a : I → R)
    (i k l : I) {T U V : Finset I} (h : T ⊆ U) (g : U ⊆ V) (hi : i ∈ T) (hk : k ∈ U) :
    finiteOverlapRestrictionCompositionComparison R i k l h g hi hk
      (FiniteOverlapKoszulObject R a l V) =
      finiteOverlapDGCompositionComparison R a i k l h g hi hk :=
  rfl

end SerrePositivity.KST.DerivedBlowup
