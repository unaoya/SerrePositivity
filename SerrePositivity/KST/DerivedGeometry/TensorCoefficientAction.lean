module

public import SerrePositivity.KST.DerivedGeometry.TensorCoefficientSheaf
public import SerrePositivity.KST.DerivedGeometry.CoefficientTensorAction
public import Mathlib.CategoryTheory.Sites.LocallySurjective

/-!
# 具体的係数環層の作用

概要：層化後の係数環層に H の作用を与え、基礎環上の両立を証明する。
方針：テンソル前層の写像を層化の単位と合成する。
規約：H の可換性・平坦性は要求しない。
使われ方：KST D4、Toën Derived Azumaya §3.2 の係数加群層。
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace SerrePositivity.KST.DerivedGeometry

variable {A : Type u} [CommRing A] (H : Type u) [Ring H] [Algebra A H]
  {X : Scheme.{u}} (a : A →+* Γ(X, ⊤))

/--
概要：H の定数前層から層化後の係数環層への写像。
方針：左因子への包含と層化の単位を合成する。
規約：定数前層の層条件を要求しない。
使われ方：KST D4、Toën §3.2 の具体的な H の作用。
-/
def tensorCoefficientConstant :
    (Functor.const (Opens X)ᵒᵖ).obj (RingCat.of H) ⟶ (tensorCoefficientSheaf H a).ring.obj :=
  coefficientTensorConstant H a ≫ tensorCoefficientComparison H a

/--
概要：層化後も H と構造層からの基礎環の作用は一致する。
方針：層化前の環準同型の等式に、比較射の各成分を後合成する。
規約：単なる加法写像ではなく環準同型の等式として述べる。
使われ方：KST D4、Toën §3.2 の A 線形係数環層 H_X。
-/
lemma tensorCoefficientConstant_comp_algebraMap (U : X.Opens) :
    ((tensorCoefficientConstant H a).app (.op U)).hom.comp (algebraMap A H) =
      (((tensorCoefficientSheaf H a).structureMap.hom).app (.op U)).hom.comp
        (sectionBaseMap a U) := by
  exact congrArg
    (fun g => ((tensorCoefficientComparison H a).app (.op U)).hom.comp g)
    (coefficientTensorConstant_comp_algebraMap H a U)

/--
概要：テンソル前層から係数環層への比較は局所全射。
方針：環の層化の単位の局所全射性を使う。
規約：大域切断上の全射性は主張しない。
使われ方：KST D4、Toën §3.2 の層化後の中心的作用の検証。
-/
instance tensorCoefficientComparison_locallySurjective :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      (tensorCoefficientComparison H a) := by
  change Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
    (toSheafify (Opens.grothendieckTopology X) (coefficientTensorPresheaf H a))
  infer_instance

/--
概要：構造層から具体的係数環層への射の像は中心的。
方針：層化の比較射の局所全射性でテンソル前層へ局所的に持ち上げ、層の分離性を使う。
規約：H の可換性や平坦性は不要。
使われ方：KST D4、Toën §3.2 の構造層上の非可換係数代数 H_X。
-/
lemma tensorCoefficientSheaf_structureMap_commutes (U : X.Opens) (r : Γ(X, U))
    (x : (tensorCoefficientSheaf H a).ring.obj.obj (.op U)) :
    Commute (((tensorCoefficientSheaf H a).structureMap.hom).app (.op U) r) x := by
  change _ * _ = _ * _
  apply (tensorCoefficientSheaf H a).ring.property.isSeparated _ _
    (Presheaf.imageSieve_mem (Opens.grothendieckTopology X)
      (tensorCoefficientComparison H a) x)
  rintro V i ⟨y, hy⟩
  simp only [map_mul]
  have hr : (tensorCoefficientSheaf H a).ring.obj.map i.op
      (((tensorCoefficientSheaf H a).structureMap.hom).app (.op U) r) =
      (((tensorCoefficientSheaf H a).structureMap.hom).app (.op V))
        (X.presheaf.map i.op r) :=
    (NatTrans.naturality_apply (tensorCoefficientSheaf H a).structureMap.hom i.op r).symm
  rw [hr, ← hy]
  exact ((coefficientTensorUnit_commutes H a V (X.presheaf.map i.op r) y).map
    ((tensorCoefficientComparison H a).app (.op V)).hom).eq

/--
概要：係数環層の各開の切断を構造層の切断上の代数にする。
方針：構造射の中心性を代数構造の可換条件に使う。
規約：作用を明示的に返し、H の非可換性を保つ。
使われ方：KST D4、Toën §3.2 の係数加群層と構造層上のテンソル積。
-/
@[instance_reducible]
def tensorCoefficientSectionAlgebra (U : X.Opens) :
    Algebra Γ(X, U) ((tensorCoefficientSheaf H a).ring.obj.obj (.op U)) where
  smul r x := (((tensorCoefficientSheaf H a).structureMap.hom).app (.op U) r) * x
  algebraMap := (((tensorCoefficientSheaf H a).structureMap.hom).app (.op U)).hom
  commutes' r x := tensorCoefficientSheaf_structureMap_commutes H a U r x
  smul_def' _ _ := rfl

end SerrePositivity.KST.DerivedGeometry
