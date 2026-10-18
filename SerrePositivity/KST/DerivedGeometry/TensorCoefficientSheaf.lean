module

public import SerrePositivity.KST.DerivedGeometry.CoefficientSheaf
public import SerrePositivity.KST.DerivedGeometry.CoefficientTensorPresheaf
public import Mathlib.CategoryTheory.Sites.ConcreteSheafification

/-!
# 具体的な非可換係数環層 H_X

概要：前層 U ↦ H ⊗_A O_X(U) を環の圏で層化して係数環層を作る。
方針：構造層からの射を、右因子への包含と層化の単位の合成で定める。
規約：平坦性・可換性を H に要求せず、アフィン切断との同型は別途証明する。
使われ方：KST D4、Toën Derived Azumaya §3.2 の D_qc(X;H) の具体的係数。
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace SerrePositivity.KST.DerivedGeometry

variable {A : Type u} [CommRing A] (H : Type u) [Ring H] [Algebra A H]
  {X : Scheme.{u}} (a : A →+* Γ(X, ⊤))

/--
概要：係数テンソル前層を層化して作る、構造層上の環層。
方針：環の圏で層化し、構造層の作用を右因子への包含から構成する。
規約：一般の開で層化前の切断と一致するとは主張しない。
使われ方：KST D4、Toën §3.2 の非可換係数環層 H_X。
-/
def tensorCoefficientSheaf : CoefficientSheaf X where
  ring := (presheafToSheaf (Opens.grothendieckTopology X) RingCat.{u}).obj
    (coefficientTensorPresheaf H a)
  structureMap :=
    { hom := coefficientTensorUnit H a ≫
        toSheafify (Opens.grothendieckTopology X) (coefficientTensorPresheaf H a) }

/--
概要：テンソル前層から具体的係数環層の基礎前層への標準写像。
方針：層化の単位を使う。
規約：アフィン上で同型であることはこの定義には含めない。
使われ方：KST D4、Toën §3.2 のアフィン dg 加群との比較。
-/
def tensorCoefficientComparison :
    coefficientTensorPresheaf H a ⟶ (tensorCoefficientSheaf H a).ring.obj :=
  toSheafify (Opens.grothendieckTopology X) (coefficientTensorPresheaf H a)

/--
概要：具体的係数環層への構造層の射は、テンソル単位と層化写像の合成。
方針：定義を展開する。
規約：層の射の基礎となる前層射についての等式。
使われ方：KST D4、Toën §3.2 の具体的係数と係数忘却の接続。
-/
lemma tensorCoefficientSheaf_structureMap :
    (tensorCoefficientSheaf H a).structureMap.hom =
      coefficientTensorUnit H a ≫ tensorCoefficientComparison H a := rfl

/--
概要：A スキームの構造射から非可換係数環層 H_X を構成する。
方針：構造射の大域切断への写像を用い、テンソル前層を層化する。
規約：H の平坦性を要求しない。
使われ方：KST D4、Toën §3.2 の D_qc(X;H) と Perf(X;H) の係数。
-/
def coefficientSheafOfMorphism (f : X ⟶ Spec (CommRingCat.of A)) : CoefficientSheaf X :=
  tensorCoefficientSheaf H (globalBaseMap f)

end SerrePositivity.KST.DerivedGeometry
