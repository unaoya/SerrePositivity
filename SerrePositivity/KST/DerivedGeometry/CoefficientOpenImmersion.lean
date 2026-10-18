module

public import SerrePositivity.KST.DerivedGeometry.CoefficientSheaf
public import SerrePositivity.KST.DerivedGeometry.OpenImmersionBase

/-!
# 開埋め込みに沿う係数環層の制限

概要：係数環層を任意の開埋め込みに沿って制限する。
方針：開像に沿う前合成と appIso の逆による構造層の輸送を使う。
規約：文字どおりの開部分の包含に限らない。
使われ方：KST D4、Toën Derived Azumaya §3.2 のアフィン同型に沿う比較。
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
概要：一般の係数環層を任意の開埋め込みに沿って制限する。
方針：開像に沿う層の制限に appIso の逆からの構造層射を添える。
規約：スキーム同型も開埋め込みとして扱う。
使われ方：KST D4、Toën §3.2 のアフィン模型の輸送。
-/
def restrictAlong {X Y : Scheme.{u}} (B : CoefficientSheaf Y) (f : X ⟶ Y)
    [IsOpenImmersion f] : CoefficientSheaf X where
  ring := (f.opensFunctor.sheafPushforwardContinuous RingCat
    (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)).obj B.ring
  structureMap.hom := openImmersionStructureMap f ≫
    Functor.whiskerLeft f.opensFunctor.op B.structureMap.hom

end SerrePositivity.KST.DerivedGeometry.CoefficientSheaf
