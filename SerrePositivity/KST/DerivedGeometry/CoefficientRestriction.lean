module

public import SerrePositivity.KST.DerivedGeometry.CoefficientSheaf
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.Topology.Sheaves.SheafCondition.Sites

/-!
# 係数環層の開部分への制限

概要：構造層からの射を持つ係数環層を開部分へ制限する。
方針：環層と構造層射を同じ開制限関手で送る。
規約：係数環の可換性を要求しない。
使われ方：KST D4、Toën Derived Azumaya §3.2 の局所係数圏。
-/

@[expose] public section

noncomputable section

set_option maxSynthPendingDepth 8
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace SerrePositivity.KST.DerivedGeometry.CoefficientSheaf

/--
概要：一般の係数環層をスキームの開部分へ制限する。
方針：環層の開制限を取り、構造層の射も制限する。
規約：開部分の構造層は元の構造層の制限として与えられる。
使われ方：KST D4、Toën §3.2 の局所化・降下の係数。
-/
def restrict {X : Scheme.{u}} (B : CoefficientSheaf X) (U : X.Opens) :
    CoefficientSheaf U.toScheme where
  ring := (U.sheafRestrict (C := RingCat)).obj B.ring
  structureMap := (U.sheafRestrict (C := RingCat)).map B.structureMap

end SerrePositivity.KST.DerivedGeometry.CoefficientSheaf
