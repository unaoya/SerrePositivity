module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineFullCoefficientRows
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.AffineEnvelopeCompletedTensorUnit
public import SerrePositivity.HomologicalAlgebra.TorBaseChange
import all SerrePositivity.HomologicalAlgebra.TorBaseChange
import all SerrePositivity.HomologicalAlgebra.Cosimplicial.Algebra
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Coefficients.AffineCoefficientDiagram
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Affine.HodgeTateAffineModel
import all SerrePositivity.BhattScholze.Prismatic.CechAlexander.Envelopes.AffineEnvelopeConstruction

/-!
# 元のfull envelopeのテンソル係数像と通常の係数射

## 概要
元の完備テンソル比較と単位の合成は、元の通常係数射の線形延長に一致する。

## 方針
同じテンソルの純テンソル表示へ帰着し、元の左右係数脚の等式を使う。

## 規約
元の環同型の選択、包、通常の係数射を保持する。

## 使われ方
R1のfull envelopeの指定同型の単位正規化を実際の係数射へ結ぶ。
-/

public noncomputable section
universe u
open CategoryTheory
open scoped TensorProduct Simplicial
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
open DerivedCompletion
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
variable {p : ℕ} [Fact p.Prime] {A B : Type u} [CommRing A] [CommRing B]
variable {P : OrientedPrism p A} {Q : OrientedPrism p B}
variable (f : OrientedPrism.Hom P Q) (hP : IsBoundedPrism P) (hQ : IsBoundedPrism Q) (r : ℕ)

/-- 同じ元のテンソル係数像は通常係数射の同じ線形延長に一致する。 -/
private theorem affineFullTensorCoefficients (n : SimplexCategory) :
    letI := f.toRingHom.toAlgebra
    let U := affineEnvelopeTerm P hP r n.len (cutoff A (affineAlgebra P r)) le_rfl
    let V := affineEnvelopeTerm Q hQ r n.len (cutoff B (affineAlgebra Q r)) le_rfl
    letI := U.X.toHom.toRingHom.toAlgebra
    let e := (exists_affineEnvelopeCoefficientBaseChange_equiv P Q f hP hQ r n.len
      (cutoff A (affineAlgebra P r)) (cutoff B (affineAlgebra Q r)) le_rfl le_rfl).choose
    ∀ z : (ModuleCat.extendScalars f.toRingHom).obj ((affineFullBaseModules P hP r).obj n),
      e (pdCompletionUnit (B ⊗[A] U.X.B) p
        (algebraMap B (B ⊗[A] U.X.B) Q.generator)
        (extendScalarsObjEquivTensor A B ((affineFullBaseModules P hP r).obj n) z)) =
      (affineFullAnyOrdinaryMap f hP hQ r).app n z := by
  let := f.toRingHom.toAlgebra
  let U := affineEnvelopeTerm P hP r n.len (cutoff A (affineAlgebra P r)) le_rfl
  let V := affineEnvelopeTerm Q hQ r n.len (cutoff B (affineAlgebra Q r)) le_rfl
  let := U.X.toHom.toRingHom.toAlgebra
  let e := (exists_affineEnvelopeCoefficientBaseChange_equiv P Q f hP hQ r n.len
    (cutoff A (affineAlgebra P r)) (cutoff B (affineAlgebra Q r)) le_rfl le_rfl).choose
  dsimp only
  intro z
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul b c =>
    change e (pdCompletionUnit (B ⊗[A] U.X.B) p
      (algebraMap B (B ⊗[A] U.X.B) Q.generator) (b ⊗ₜ[A] c)) = _
    rw [affineFullAnyOrdinaryMap_tmul]
    change e (pdCompletionUnit (B ⊗[A] U.X.B) p
      (algebraMap B (B ⊗[A] U.X.B) Q.generator) (b ⊗ₜ[A] c)) =
      V.X.toHom.toRingHom b * affineEnvelopeCoefficientMap f U V c
    exact affineEnvelopeCompletedTensor_tmul P Q hP hQ f r n.len
      (cutoff A (affineAlgebra P r)) (cutoff B (affineAlgebra Q r)) le_rfl le_rfl b c

end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
