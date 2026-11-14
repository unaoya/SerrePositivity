module
public meta import SerrePositivity.Util.Citation

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.BaseChange.AffineEnvelopeBaseChangeCoefficients
public import SerrePositivity.BhattScholze.Prismatic.Envelopes.CompletedFreeDeltaFlat
public import SerrePositivity.BhattScholze.Prism.Bounded.CompletedTensorH0
public import SerrePositivity.BhattScholze.Prism.Bounded.CompletedTensorCover
import all SerrePositivity.BhattScholze.Prismatic.CechAlexander.Envelopes.AffineEnvelopeConstruction
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.WittAffineBaseChange
import all SerrePositivity.BhattScholze.Prism.Bounded.CompletedTensorCover

/-!
# 有限 affine 包の完備テンソルによる導来底変換の計算

## 概要
標準の有限 affine 包の項の完備テンソル積は、二座標完備導来底変換そのものを計算する。

## 方針
完備自由 δ 環の (p,d) 完全平坦性を底変換し、有界 prism 上の離散性を適用する。
既存の H⁰ の係数線形同型で、実際の完備テンソルの single 対象に移す。

## 規約
両方の基底は有界 prism。係数の環射自体の通常の平坦性は要求しない。
完備テンソルの加群構造は既存の左係数脚によるもの。

## 使われ方
BS 著者版 Proposition 3.13 (2)、Theorem 6.4 の有限 affine 枠の項ごとの導来計算。
-/

public noncomputable section

open CategoryTheory SerrePositivity.DerivedCompletion

universe u

namespace SerrePositivity.BhattScholze.Prismatic

set_option backward.isDefEq.respectTransparency false
attribute [local instance] HasDerivedCategory.standard

variable {p : ℕ} [Fact p.Prime] {A B : Type u} [CommRing A] [CommRing B]
variable (P : OrientedPrism p A) (Q : OrientedPrism p B)
variable (hP : IsBoundedPrism P) (hQ : IsBoundedPrism Q) (f : OrientedPrism.Hom P Q)
variable (r n : ℕ) (κ : Cardinal.{u})
variable (hκ : cutoff A (prismPolynomialCompletion P (Fin r)) ≤ κ)

local notation "U" => affineEnvelopeTerm P hP r n κ hκ

/-- 標準の有限 affine 包は、基底の (p,d) について完全平坦。 -/
theorem affineEnvelopeTerm_completelyFlat :
    let := (U).X.toHom.toRingHom.toAlgebra
    IsCompletelyFlat (Ideal.span {(p : A), P.generator}) (U).X.B := by
  rw [standard_affine_base P hP r n κ hκ]
  exact completedFreeDelta_completelyFlat P hP (AffineIndex.{u} r n)

/-- 各項の実際の完備テンソル積が、完備導来底変換を計算する。 -/
def affineEnvelopeTermCompletedBaseChangeIso :
    letI := f.toRingHom.toAlgebra
    letI := (U).X.toHom.toRingHom.toAlgebra
    let T := PrismCompletedTensor (A := A) (C := (U).X.B) Q
    letI := (prismCompletedTensorLeft Q (A := A) (C := (U).X.B)).toAlgebra
    let Y := pairCompletedBaseChange f.toRingHom (p : B) Q.generator
      (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of A (U).X.B))
    Y.obj ≅ (DerivedCategory.singleFunctor (ModuleCat B) 0).obj (ModuleCat.of B T) := by
  let := f.toRingHom.toAlgebra
  let := (U).X.toHom.toRingHom.toAlgebra
  let T := PrismCompletedTensor (A := A) (C := (U).X.B) Q
  let := (prismCompletedTensorLeft Q (A := A) (C := (U).X.B)).toAlgebra
  let I := Ideal.span {(p : A), P.generator}
  let J := Ideal.span {(p : B), Q.generator}
  have hg : I.map f.toRingHom = J := by
    change (Ideal.span {(p : A), P.generator}).map f.toRingHom = _
    rw [← Set.singleton_union, Ideal.span_union, Ideal.map_sup, Ideal.map_span,
      Set.image_singleton, map_natCast]
    change Ideal.span {(p : B)} ⊔ P.ideal.map f.toRingHom = _
    rw [f.map_ideal_eq, OrientedPrism.ideal, ← Ideal.span_union, Set.singleton_union]
  let Y := pairCompletedBaseChange f.toRingHom (p : B) Q.generator
    (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of A (U).X.B))
  have hY : IsDerivedCompletelyFlat J Y :=
    pairCompletedBaseChange_completelyFlat f.toRingHom I (p : B) Q.generator hg
      (affineEnvelopeTerm_completelyFlat P hP r n κ hκ)
  have hd : IsComplete B Q.generator Y.obj :=
    derivedComplexCompletionFunctor_isComplete B Q.generator _
  have hp : IsComplete B (p : B) Y.obj :=
    complete_completion_of_complete (p : B) Q.generator _
      (derivedComplexCompletionFunctor_isComplete B (p : B) _)
  have ht := derivedCompletelyFlat_isDiscrete_of_boundedPrism Q hQ Y hp hd hY
  let := ht.1
  let := ht.2.1
  exact normalizedPureHomologyIso Y.obj 0 ≪≫
    (DerivedCategory.singleFunctor (ModuleCat B) 0).mapIso
      (pairCompletedBaseChangeH0LinearEquiv (A := A) (C := (U).X.B) Q).toModuleIso

variable (κ' : Cardinal.{u})
variable (hκ' : cutoff B (prismPolynomialCompletion Q (Fin r)) ≤ κ')

local notation "V" => affineEnvelopeTerm Q hQ r n κ' hκ'

/-- 完備導来底変換を、標準の係数変更先の有限 affine 項そのもので計算する。 -/
def affineEnvelopeTermCompletedBaseChangeToTargetIso :
    letI := f.toRingHom.toAlgebra
    letI := (U).X.toHom.toRingHom.toAlgebra
    letI := (V).X.toHom.toRingHom.toAlgebra
    let Y := pairCompletedBaseChange f.toRingHom (p : B) Q.generator
      (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of A (U).X.B))
    Y.obj ≅ (DerivedCategory.singleFunctor (ModuleCat B) 0).obj (ModuleCat.of B (V).X.B) := by
  let := f.toRingHom.toAlgebra
  let := (U).X.toHom.toRingHom.toAlgebra
  let := (V).X.toHom.toRingHom.toAlgebra
  let T := PrismCompletedTensor (A := A) (C := (U).X.B) Q
  let l := prismCompletedTensorLeft Q (A := A) (C := (U).X.B)
  let := l.toAlgebra
  let H := exists_affineEnvelopeCoefficientBaseChange_equiv P Q f hP hQ r n κ κ' hκ hκ'
  let e := H.choose
  have he := H.choose_spec.2
  let el : T ≃ₗ[B] (V).X.B :=
    { e.toAddEquiv with
      map_smul' := by
        intro b x
        change e (l b * x) = (V).X.toHom.toRingHom b * e x
        have hb : e (l b) = (V).X.toHom.toRingHom b := RingHom.congr_fun he b
        rw [map_mul, hb] }
  exact affineEnvelopeTermCompletedBaseChangeIso P Q hP hQ f r n κ hκ ≪≫
    (DerivedCategory.singleFunctor (ModuleCat B) 0).mapIso el.toModuleIso

end SerrePositivity.BhattScholze.Prismatic

/-! Reviewed literature correspondences. -/
attribute [cite BS19 "Rem 4.19" (partial := component) "BS-W17 H4（11-11）：affine の小さい模型、底変換との項ごとの両立（δ 同型・脚・座標、全単体射に自然）は本体。「Δ を計算する」主張と Tot の底変換は G10 の後。項ごとの導来底変換の同型も本体（AffineEnvelopeDerivedBaseChange） ／ 11-12 夜更新（§4 の見直し）"] _root_.SerrePositivity.BhattScholze.Prismatic.affineEnvelopeTermCompletedBaseChangeIso
