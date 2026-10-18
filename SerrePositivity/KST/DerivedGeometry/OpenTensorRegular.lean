module

public import SerrePositivity.KST.DerivedGeometry.OpenTensorSheaf
public import SerrePositivity.KST.DerivedGeometry.CoefficientRegularRestriction

/-!
# 具体的係数環層の正則加群と開制限

概要：開部分で直接構成した係数環層の正則 O 加群を大域正則加群の制限と同定する。
方針：構造層射を保つ環層同型と正則加群の制限同型を合成する。
規約：Mathlib の構造層加群の開制限関手との同型として述べる。
使われ方：KST D4・T1、Toën Derived Azumaya §3.2 の準連接性の局所判定。
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
  {X : Scheme.{u}} (a : A →+* Γ(X, ⊤)) (U : X.Opens)

/--
概要：開部分での直接構成の正則 O 加群は大域構成の正則 O 加群の制限と同型。
方針：係数環層の開制限同型を正則加群へ移し、加群制限の同型と合成する。
規約：開部分上の実際の O 加群層の同型。
使われ方：KST D4・T1、Toën §3.2 の局所的なアフィン模型。
-/
def openTensorRegularIso :
    (tensorCoefficientSheaf H (restrictedBaseMap a U)).regular ≅
      (Scheme.Modules.restrictFunctor U.ι).obj (tensorCoefficientSheaf H a).regular :=
  asIso (CoefficientSheaf.regularMap (openTensorSheafIso H a U).hom
    (openTensorSheafIso_structureMap H a U)) ≪≫
  (CoefficientSheaf.regularRestrictIso (tensorCoefficientSheaf H a) U).symm

/--
概要：構造射から構成した係数環層の正則 O 加群も開制限と可換。
方針：構造射を制限した基礎環写像の計算と正則加群の開制限同型を使う。
規約：制限した構造射は U.ι との合成とする。
使われ方：KST D4・T1、Toën §3.2 の実際の係数層の局所比較。
-/
def coefficientSheafOfMorphism_regularRestrictIso (f : X ⟶ Spec (CommRingCat.of A)) :
    (coefficientSheafOfMorphism H (U.ι ≫ f)).regular ≅
      (Scheme.Modules.restrictFunctor U.ι).obj (coefficientSheafOfMorphism H f).regular :=
  openTensorRegularIso H (globalBaseMap f) U

end SerrePositivity.KST.DerivedGeometry
