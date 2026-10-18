module

public import SerrePositivity.KST.DerivedGeometry.AffineSchemeCoefficient
public import SerrePositivity.KST.DerivedGeometry.QuasicoherentOpenCriterion
public import SerrePositivity.KST.DerivedGeometry.OpenTensorRegular

/-!
# 具体的係数環層の準連接性

概要：任意のスキーム上で具体的係数環層の正則 O 加群は準連接。
方針：全アフィン開の被覆、アフィンの場合の定理、開制限の比較を使う。
規約：H の平坦性・可換性やスキームの分離性を要求しない。
使われ方：KST D4・T1、Bondal–van den Bergh Thm 3.1.1、Toën §3.2 の係数。
-/

@[expose] public section

noncomputable section

set_option maxSynthPendingDepth 8
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry

namespace SerrePositivity.KST.DerivedGeometry

variable {A : Type u} [CommRing A] (H : Type u) [Ring H] [Algebra A H]
  {X : Scheme.{u}} (a : A →+* Γ(X, ⊤))

/--
概要：具体的係数環層の正則 O 加群は任意のスキーム上で準連接。
方針：アフィン開での直接構成の準連接性を制限の同型で移し、被覆上で判定する。
規約：準コンパクト性・準分離性・平坦性はこの主張には不要。
使われ方：KST D4・T1、Bondal–van den Bergh Thm 3.1.1、Toën §3.2 の係数環層。
-/
instance tensorCoefficientRegular_isQuasicoherent :
    (tensorCoefficientSheaf H a).regular.IsQuasicoherent := by
  have (U : X.affineOpens) :
      ((Scheme.Modules.restrictFunctor U.1.ι).obj
        (tensorCoefficientSheaf H a).regular).IsQuasicoherent := by
    let : IsAffine U.1.toScheme := U.2
    exact (SheafOfModules.isQuasicoherent U.1.toScheme.ringCatSheaf).prop_of_iso
      (openTensorRegularIso H a U.1)
      (affineSchemeCoefficientRegular_isQuasicoherent (restrictedBaseMap a U.1) H)
  exact module_isQuasicoherent_of_openCover (tensorCoefficientSheaf H a).regular
    (fun U : X.affineOpens => U.1) (iSup_affineOpens_eq_top X)

/--
概要：実際の構造射から構成した係数環層の正則 O 加群は準連接。
方針：構造射が誘導する基礎環写像に一般の準連接性の定理を適用する。
規約：導来圏の生成や降下はこの層の定理に含まれない。
使われ方：KST D4・T1、Toën §3.2 の D_qc の幾何的係数。
-/
instance coefficientSheafOfMorphism_regular_isQuasicoherent
    (f : X ⟶ Spec (CommRingCat.of A)) :
    (coefficientSheafOfMorphism H f).regular.IsQuasicoherent :=
  tensorCoefficientRegular_isQuasicoherent H (globalBaseMap f)

end SerrePositivity.KST.DerivedGeometry
