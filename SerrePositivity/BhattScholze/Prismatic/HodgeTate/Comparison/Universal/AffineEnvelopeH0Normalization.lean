module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.BaseChange.AffineEnvelopeDerivedBaseChange
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.PureHomologyPostcomposition
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.BaseChange.AffineEnvelopeDerivedBaseChange

/-!
# 元のfull envelopeの完備底変換同型のH⁰

## 概要
元のfull envelopeの指定同型は、元の完備テンソル積のH⁰線形同型を誘導する。

## 方針
既存の純ホモロジー同型の正規化を元の定義に適用する。

## 規約
元のaffineEnvelopeTermCompletedBaseChangeIsoを保持する。

## 使われ方
R1の元のfull envelopeの係数単位の照合に使う。
-/

public noncomputable section
universe u
open CategoryTheory
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
open DerivedCompletion
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
variable {p : ℕ} [Fact p.Prime] {A B : Type u} [CommRing A] [CommRing B]
variable (P : OrientedPrism p A) (Q : OrientedPrism p B)
variable (hP : IsBoundedPrism P) (hQ : IsBoundedPrism Q) (f : OrientedPrism.Hom P Q)
variable (r n : ℕ) (κ : Cardinal.{u})
variable (hκ : cutoff A (prismPolynomialCompletion P (Fin r)) ≤ κ)

/-- 元の指定同型のH⁰写像は、元の完備テンソル積の同じ線形同型。 -/
theorem affineEnvelopeTermCompletedBaseChangeIso_homology :
    letI := f.toRingHom.toAlgebra
    let U := affineEnvelopeTerm P hP r n κ hκ
    letI := U.X.toHom.toRingHom.toAlgebra
    let T := PrismCompletedTensor (A := A) (C := U.X.B) Q
    letI := (prismCompletedTensorLeft Q (A := A) (C := U.X.B)).toAlgebra
    (DerivedCategory.homologyFunctor (ModuleCat.{u} B) 0).map
        (affineEnvelopeTermCompletedBaseChangeIso P Q hP hQ f r n κ hκ).hom ≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} B) 0).hom.app
        (ModuleCat.of B T) =
      (pairCompletedBaseChangeH0LinearEquiv (A := A) (C := U.X.B) Q).toModuleIso.hom := by
  let := f.toRingHom.toAlgebra
  let U := affineEnvelopeTerm P hP r n κ hκ
  let := U.X.toHom.toRingHom.toAlgebra
  let T := PrismCompletedTensor (A := A) (C := U.X.B) Q
  let := (prismCompletedTensorLeft Q (A := A) (C := U.X.B)).toAlgebra
  let Y := pairCompletedBaseChange f.toRingHom (p : B) Q.generator
    (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of A U.X.B))
  let e := affineEnvelopeTermCompletedBaseChangeIso P Q hP hQ f r n κ hκ
  let : Y.obj.IsGE 0 := DerivedCategory.TStructure.t.isGE_of_iso e.symm 0
  let : Y.obj.IsLE 0 := DerivedCategory.TStructure.t.isLE_of_iso e.symm 0
  change (DerivedCategory.homologyFunctor (ModuleCat.{u} B) 0).map
    ((normalizedPureHomologyIso Y.obj 0).hom ≫
      (DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).map
        (pairCompletedBaseChangeH0LinearEquiv (A := A) (C := U.X.B) Q).toModuleIso.hom) ≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} B) 0).hom.app _ = _
  exact normalizedPureHomologyIso_postcomp 0 Y.obj (ModuleCat.of B T) _

end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
