module

public import SerrePositivity.KST.DerivedGeometry.AffineBaseChangeSheaf
public import SerrePositivity.KST.DerivedGeometry.CoefficientRegularMap
public import SerrePositivity.KST.DerivedGeometry.AffineCoefficientQuasicoherent

/-!
# 一般の基礎環に対するアフィン係数環層の準連接性

概要：A → R に対する係数環層の正則 O 加群を tilde (H ⊗_A R) と同定する。
方針：構造層射と両立する環層の底変換同型で正則加群の同型を作る。
規約：H の平坦性・可換性を要求しない。一般の X への局所化は別定理。
使われ方：KST D4・T1、Bondal–van den Bergh Thm 3.1.1、Toën §3.2。
-/

@[expose] public section

noncomputable section

set_option maxSynthPendingDepth 8
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace SerrePositivity.KST.DerivedGeometry

variable (A : Type u) [CommRing A] (R : CommRingCat.{u}) [Algebra A R]
  (H : Type u) [Ring H] [Algebra A H]

/--
概要：一般の基礎環からの係数底変換は正則 O 加群の同型を与える。
方針：構造層射と可換な環層同型から正則加群の同型を構成する。
規約：H ⊗_A R の R 作用は右因子から与える。
使われ方：KST D4、Toën §3.2 の準連接性の移送。
-/
def affineCoefficientBaseChangeRegularIso :
    letI : Algebra R (H ⊗[A] R) := Algebra.TensorProduct.rightAlgebra
    (tensorCoefficientSheaf (H ⊗[A] R) (Scheme.ΓSpecIso R).inv.hom).regular ≅
      (tensorCoefficientSheaf H (affineBaseMap A R)).regular := by
  letI : Algebra R (H ⊗[A] R) := Algebra.TensorProduct.rightAlgebra
  exact asIso (CoefficientSheaf.regularMap (affineCoefficientBaseChangeSheafIso A R H).hom
    (affineCoefficientBaseChangeSheafIso_structureMap A R H))

/--
概要：A → R に対する係数環層の正則 O 加群は tilde (H ⊗_A R) と同型。
方針：R 係数での tilde の同型と底変換の正則加群同型を合成する。
規約：左辺の tilde の係数は右因子由来の R 加群。
使われ方：KST D4・T1、Toën §3.2 のアフィン局所模型。
-/
def affineBaseCoefficientModuleIso :
    letI : Algebra R (H ⊗[A] R) := Algebra.TensorProduct.rightAlgebra
    tilde (ModuleCat.of R (H ⊗[A] R)) ≅
      (tensorCoefficientSheaf H (affineBaseMap A R)).regular := by
  letI : Algebra R (H ⊗[A] R) := Algebra.TensorProduct.rightAlgebra
  exact affineCoefficientModuleIso (H ⊗[A] R) ≪≫ affineCoefficientBaseChangeRegularIso A R H

/--
概要：任意の A → R に対しアフィン係数環層の正則 O 加群は準連接。
方針：構成した tilde の同型で準連接性を移送する。
規約：平坦性は不要であり、導来生成や降下はこの定理に含めない。
使われ方：KST D4・T1、Bondal–van den Bergh Thm 3.1.1、Toën §3.2。
-/
instance affineBaseCoefficientRegular_isQuasicoherent :
    (tensorCoefficientSheaf H (affineBaseMap A R)).regular.IsQuasicoherent := by
  let : Algebra R (H ⊗[A] R) := Algebra.TensorProduct.rightAlgebra
  exact (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso
    (affineBaseCoefficientModuleIso A R H) inferInstance

/--
概要：実際の Spec R → Spec A から構成した係数環層の正則 O 加群は準連接。
方針：構造射からの基礎環写像を affineBaseMap に同定する。
規約：構造射は与えられた A 代数構造によるもの。
使われ方：KST D4・T1、Toën §3.2 のスキーム上の係数環層への接続。
-/
instance coefficientSheafOfSpecMap_regular_isQuasicoherent :
    (coefficientSheafOfMorphism H
      (Spec.map (CommRingCat.ofHom (algebraMap A R)))).regular.IsQuasicoherent := by
  change (tensorCoefficientSheaf H
    (globalBaseMap (Spec.map (CommRingCat.ofHom (algebraMap A R))))).regular.IsQuasicoherent
  rw [globalBaseMap_spec]
  infer_instance

end SerrePositivity.KST.DerivedGeometry
