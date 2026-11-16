module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineEnvelopeH0Normalization
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.PairCompletedH0Unit
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.BaseChange.AffineEnvelopeDerivedBaseChange

/-!
# 元のfull envelopeの被覆同型と二回完備化単位のH⁰

## 概要
元の標的への指定同型と二回完備化単位の合成を、元の係数テンソルの像で計算する。

## 方針
同じ選択された完備テンソル同型の左係数脚と、元のH⁰正規化を使う。

## 規約
既存のaffineEnvelopeTermCompletedBaseChangeToTargetIsoに使われた同じ選択を保持する。

## 使われ方
R1の項ごとの元の係数射の一致をfull envelope上で証明する。
-/

public noncomputable section
universe u
open CategoryTheory
open scoped TensorProduct
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
open DerivedCompletion
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
variable {p : ℕ} [Fact p.Prime] {A B : Type u} [CommRing A] [CommRing B]
variable (P : OrientedPrism p A) (Q : OrientedPrism p B)
variable (hP : IsBoundedPrism P) (hQ : IsBoundedPrism Q) (f : OrientedPrism.Hom P Q)
variable (r n : ℕ) (κ κ' : Cardinal.{u})
variable (hκ : cutoff A (prismPolynomialCompletion P (Fin r)) ≤ κ)
variable (hκ' : cutoff B (prismPolynomialCompletion Q (Fin r)) ≤ κ')

/-- 元のfull envelopeの指定比較は、二回の元の単位を同じ完備テンソルの係数像へ送る。 -/
theorem affineEnvelopeTargetH0_unit :
    letI := f.toRingHom.toAlgebra
    let U := affineEnvelopeTerm P hP r n κ hκ
    let V := affineEnvelopeTerm Q hQ r n κ' hκ'
    letI := U.X.toHom.toRingHom.toAlgebra
    letI := V.X.toHom.toRingHom.toAlgebra
    let H := DerivedCategory.homologyFunctor (ModuleCat.{u} B) 0
    let Y := ((boundedAboveDerivedBaseChange f.toRingHom).obj
      (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of A U.X.B))).obj
    let e := (exists_affineEnvelopeCoefficientBaseChange_equiv P Q f hP hQ r n
      κ κ' hκ hκ').choose
    ∀ x : H.obj Y,
      ((H.map ((derivedComplexCompletionUnit B (p : B)).app Y ≫
          (derivedComplexCompletionUnit B Q.generator).app
            ((derivedComplexCompletionFunctor B (p : B)).obj Y)) ≫
        H.map (affineEnvelopeTermCompletedBaseChangeToTargetIso P Q hP hQ f r n
          κ hκ κ' hκ').hom) ≫
        (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} B) 0).hom.app
          (ModuleCat.of B V.X.B)) x =
      e (pdCompletionUnit (B ⊗[A] U.X.B) p (algebraMap B (B ⊗[A] U.X.B) Q.generator)
        ((H.map ((boundedAboveDerivedBaseChangeModuleAugmentation f.toRingHom).app
          (ModuleCat.of A U.X.B)) ≫
          (realizedSingleH0Iso B).hom.app
            ((ModuleCat.extendScalars f.toRingHom).obj (ModuleCat.of A U.X.B)) ≫
          (extendScalarsObjEquivTensor A B (ModuleCat.of A U.X.B)).toModuleIso.hom) x)) := by
  let := f.toRingHom.toAlgebra
  let U := affineEnvelopeTerm P hP r n κ hκ
  let V := affineEnvelopeTerm Q hQ r n κ' hκ'
  let := U.X.toHom.toRingHom.toAlgebra
  let := V.X.toHom.toRingHom.toAlgebra
  let T := PrismCompletedTensor (A := A) (C := U.X.B) Q
  let l := prismCompletedTensorLeft Q (A := A) (C := U.X.B)
  let := l.toAlgebra
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} B) 0
  let eH := exists_affineEnvelopeCoefficientBaseChange_equiv P Q f hP hQ r n κ κ' hκ hκ'
  let e := eH.choose
  let el : T ≃ₗ[B] V.X.B :=
    { e.toAddEquiv with
      map_smul' := by
        intro b x
        change e (l b * x) = V.X.toHom.toRingHom b * e x
        have hl : e (l b) = V.X.toHom.toRingHom b := RingHom.congr_fun eH.choose_spec.2 b
        rw [map_mul, hl] }
  let ε := DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} B) 0
  have hn := ε.hom.naturality el.toModuleIso.hom
  change H.map ((DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).map el.toModuleIso.hom) ≫
      ε.hom.app (ModuleCat.of B V.X.B) = ε.hom.app (ModuleCat.of B T) ≫ el.toModuleIso.hom at hn
  have hb := affineEnvelopeTermCompletedBaseChangeIso_homology P Q hP hQ f r n κ hκ
  have ht : H.map (affineEnvelopeTermCompletedBaseChangeToTargetIso P Q hP hQ f r n
      κ hκ κ' hκ').hom ≫ ε.hom.app (ModuleCat.of B V.X.B) =
      (pairCompletedBaseChangeH0LinearEquiv (A := A) (C := U.X.B) Q).toModuleIso.hom ≫
        el.toModuleIso.hom := by
    change H.map ((affineEnvelopeTermCompletedBaseChangeIso P Q hP hQ f r n κ hκ).hom ≫
      (DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).map el.toModuleIso.hom) ≫ _ = _
    rw [Functor.map_comp, Category.assoc, hn, ← Category.assoc, hb]
  dsimp only
  intro x
  rw [Category.assoc, ht]
  change e (pairCompletedBaseChangeH0LinearEquiv (A := A) (C := U.X.B) Q
    (H.map _ x)) = _
  exact congrArg e (pairCompletedBaseChangeH0LinearEquiv_unit (A := A) (C := U.X.B) Q x)

end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
