module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.BaseChange.AffineEnvelopeBaseChangeCoefficients
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.Comparison.CrystallineCompletedTensor
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PointwiseTensor
import all SerrePositivity.BhattScholze.Prismatic.CechAlexander.Envelopes.AffineEnvelopeConstruction
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.Comparison.CrystallineCompletedTensor
import all SerrePositivity.BhattScholze.Prism.Bounded.CompletedTensor
import all SerrePositivity.HomologicalAlgebra.DerivedCompletion.PointwiseTensor

/-!
# 結晶的な係数への有限 affine 項の完備係数拡大

## 概要
有限 affine 項の各項の完備係数拡大を、係数変更先の実際の affine 項に同定する。

## 方針
二座標の完備テンソルの存在定理を使い、結晶的な終域では主完備化に書き直す。

## 規約
両基底は有界 prism、終域の生成元は p。元の係数射の通常の平坦性は仮定しない。

## 使われ方
BS 著者版 Theorem 6.4、Witt の橋の各項の係数変更。
-/

public noncomputable section
open CategoryTheory
open scoped TensorProduct ChangeOfRings
open SerrePositivity.DerivedCompletion
universe u
namespace SerrePositivity.BhattScholze.Prismatic
set_option backward.isDefEq.respectTransparency false
variable {p : ℕ} [Fact p.Prime] {A B : Type u} [CommRing A] [CommRing B]
variable (P : OrientedPrism p A) (Q : OrientedPrism p B)
variable (hP : IsBoundedPrism P) (hQ : IsBoundedPrism Q) (hg : Q.generator = (p : B))
variable (f : OrientedPrism.Hom P Q) (r n : ℕ) (κ κ' : Cardinal.{u})
variable (hκ : cutoff A (prismPolynomialCompletion P (Fin r)) ≤ κ)
variable (hκ' : cutoff B (prismPolynomialCompletion Q (Fin r)) ≤ κ')
local notation "U" => affineEnvelopeTerm P hP r n κ hκ
local notation "V" => affineEnvelopeTerm Q hQ r n κ' hκ'

private def baseChangeEquiv :
    letI := f.toRingHom.toAlgebra
    letI := (U).X.toHom.toRingHom.toAlgebra
    PrismCompletedTensor (A := A) (C := (U).X.B) Q ≃+* (V).X.B :=
  (exists_affineEnvelopeCoefficientBaseChange_equiv P Q f hP hQ r n κ κ' hκ hκ').choose

private theorem baseChangeEquiv_left :
    letI := f.toRingHom.toAlgebra
    letI := (U).X.toHom.toRingHom.toAlgebra
    (baseChangeEquiv P Q hP hQ f r n κ κ' hκ hκ').toRingHom.comp
      (prismCompletedTensorLeft Q) = (V).X.toHom.toRingHom :=
  (exists_affineEnvelopeCoefficientBaseChange_equiv P Q f hP hQ r n κ κ' hκ hκ').choose_spec.2

private theorem baseChangeEquiv_right :
    letI := f.toRingHom.toAlgebra
    letI := (U).X.toHom.toRingHom.toAlgebra
    (baseChangeEquiv P Q hP hQ f r n κ κ' hκ hκ').toRingHom.comp
      (prismCompletedTensorRight Q) = affineEnvelopeCoefficientMap f U V :=
  (exists_affineEnvelopeCoefficientBaseChange_equiv P Q f hP hQ r n κ κ' hκ hκ').choose_spec.1

/-- 結晶的な係数への通常テンソルの主完備環を、実際の affine 項に同定する。 -/
def affineEnvelopeCompletedTensorRingEquiv :
    letI := f.toRingHom.toAlgebra
    letI := (U).X.toHom.toRingHom.toAlgebra
    CompletedRing p (B ⊗[A] (U).X.B) ≃+* (V).X.B := by
  let := f.toRingHom.toAlgebra
  let := (U).X.toHom.toRingHom.toAlgebra
  exact (crystallineCompletedTensorRingEquiv (C := (U).X.B) Q hg).symm.trans
    (baseChangeEquiv P Q hP hQ f r n κ κ' hκ hκ')

/-- 比較は左係数の脚を保つ。 -/
theorem affineEnvelopeCompletedTensorRingEquiv_left (b : B) :
    letI := f.toRingHom.toAlgebra
    letI := (U).X.toHom.toRingHom.toAlgebra
    affineEnvelopeCompletedTensorRingEquiv P Q hP hQ hg f r n κ κ' hκ hκ'
      (principalCompletionRingCatUnit p (CommRingCat.of (B ⊗[A] (U).X.B))
        (b ⊗ₜ[A] (1 : (U).X.B))) = (V).X.toHom.toRingHom b := by
  let := f.toRingHom.toAlgebra
  let := (U).X.toHom.toRingHom.toAlgebra
  let e := crystallineCompletedTensorRingEquiv (A := A) (C := (U).X.B) Q hg
  have hi : e.symm
      (principalCompletionRingCatUnit p (CommRingCat.of (B ⊗[A] (U).X.B)) (b ⊗ₜ[A] 1)) =
      prismCompletedTensorLeft Q b := by
    apply e.injective
    rw [RingEquiv.apply_symm_apply]
    exact (crystallineCompletedTensorRingEquiv_left Q hg b).symm
  change baseChangeEquiv P Q hP hQ f r n κ κ' hκ hκ' (e.symm _) = _
  rw [hi]
  exact RingHom.congr_fun (baseChangeEquiv_left P Q hP hQ f r n κ κ' hκ hκ') b

/-- 比較の右脚は指定された affine 係数変更そのもの。 -/
theorem affineEnvelopeCompletedTensorRingEquiv_right (x : (U).X.B) :
    letI := f.toRingHom.toAlgebra
    letI := (U).X.toHom.toRingHom.toAlgebra
    affineEnvelopeCompletedTensorRingEquiv P Q hP hQ hg f r n κ κ' hκ hκ'
      (principalCompletionRingCatUnit p (CommRingCat.of (B ⊗[A] (U).X.B))
        ((1 : B) ⊗ₜ[A] x)) = affineEnvelopeCoefficientMap f U V x := by
  let := f.toRingHom.toAlgebra
  let := (U).X.toHom.toRingHom.toAlgebra
  let e := crystallineCompletedTensorRingEquiv (A := A) (C := (U).X.B) Q hg
  have hi : e.symm
      (principalCompletionRingCatUnit p (CommRingCat.of (B ⊗[A] (U).X.B)) (1 ⊗ₜ[A] x)) =
      prismCompletedTensorRight Q x := by
    apply e.injective
    rw [RingEquiv.apply_symm_apply]
    exact (crystallineCompletedTensorRingEquiv_right Q hg x).symm
  change baseChangeEquiv P Q hP hQ f r n κ κ' hκ hκ' (e.symm _) = _
  rw [hi]
  exact RingHom.congr_fun (baseChangeEquiv_right P Q hP hQ f r n κ κ' hκ hκ') x

/-- 左係数上で実際の affine 項へ移す代数同型。 -/
def affineEnvelopeCompletedTensorAlgEquiv :
    letI := f.toRingHom.toAlgebra
    letI := (U).X.toHom.toRingHom.toAlgebra
    letI := (V).X.toHom.toRingHom.toAlgebra
    CompletedRing p (B ⊗[A] (U).X.B) ≃ₐ[B] (V).X.B := by
  let := f.toRingHom.toAlgebra
  let := (U).X.toHom.toRingHom.toAlgebra
  let := (V).X.toHom.toRingHom.toAlgebra
  exact { affineEnvelopeCompletedTensorRingEquiv P Q hP hQ hg f r n κ κ' hκ hκ' with
    commutes' := affineEnvelopeCompletedTensorRingEquiv_left P Q hP hQ hg f r n κ κ' hκ hκ' }

/-- 各項の完備係数拡大関手の値を、実際の有限 affine 項と同定する。 -/
def affineEnvelopePointwiseCoefficientIso :
    letI := f.toRingHom.toAlgebra
    letI := (U).X.toHom.toRingHom.toAlgebra
    letI := (V).X.toHom.toRingHom.toAlgebra
    (pCompletedScalarExtensionFunctor p f.toRingHom).obj (ModuleCat.of A (U).X.B) ≅
      ModuleCat.of B (V).X.B := by
  let := f.toRingHom.toAlgebra
  let := (U).X.toHom.toRingHom.toAlgebra
  let := (V).X.toHom.toRingHom.toAlgebra
  exact pCompletedScalarExtensionTensorIso p A B (U).X.B ≪≫
    (affineEnvelopeCompletedTensorAlgEquiv P Q hP hQ hg f r n κ κ' hκ hκ').toLinearEquiv.toModuleIso

/-- 各項の線形比較は、右脚の単位上で指定された affine 係数変更を与える。 -/
theorem affineEnvelopePointwiseCoefficientIso_unit (x : (U).X.B) :
    letI := f.toRingHom.toAlgebra
    letI := (U).X.toHom.toRingHom.toAlgebra
    letI := (V).X.toHom.toRingHom.toAlgebra
    (affineEnvelopePointwiseCoefficientIso P Q hP hQ hg f r n κ κ' hκ hκ').hom
      (((moduleCompletionH0Unit B (p : B)).app
        ((ModuleCat.extendScalars f.toRingHom).obj (ModuleCat.of A (U).X.B)))
          ((1 : B) ⊗ₜ[A,f.toRingHom] x)) = affineEnvelopeCoefficientMap f U V x := by
  let := f.toRingHom.toAlgebra
  let := (U).X.toHom.toRingHom.toAlgebra
  let := (V).X.toHom.toRingHom.toAlgebra
  change affineEnvelopeCompletedTensorRingEquiv P Q hP hQ hg f r n κ κ' hκ hκ'
    ((pCompletedScalarExtensionTensorIso p A B (U).X.B).hom _) = _
  exact (congrArg (affineEnvelopeCompletedTensorRingEquiv P Q hP hQ hg f r n κ κ' hκ hκ')
    (pCompletedScalarExtensionTensorIso_unit p A B (U).X.B (1 : B) x)).trans
      (affineEnvelopeCompletedTensorRingEquiv_right P Q hP hQ hg f r n κ κ' hκ hκ' x)

end SerrePositivity.BhattScholze.Prismatic
