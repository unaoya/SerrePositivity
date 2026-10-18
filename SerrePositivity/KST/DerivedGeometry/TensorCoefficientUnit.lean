module

public import SerrePositivity.KST.DerivedGeometry.TensorCoefficientAction

/-!
# 基礎環を係数とした場合の構造層の回復

概要：H = A の係数環層が構造層と標準的に同型であることを証明する。
方針：各開の A ⊗_A O_X(U) ≃ O_X(U) を前層の同型にし、層化へ移す。
規約：一般の H のアフィン切断との同定は別の主張である。
使われ方：KST D4、Bondal–van den Bergh Thm 3.1.1、Toën §3.2 の通常係数への接続。
-/

@[expose] public section

noncomputable section

set_option maxSynthPendingDepth 8
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace SerrePositivity.KST.DerivedGeometry

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (a : A →+* Γ(X, ⊤))

/--
概要：H = A のとき、構造層からテンソル前層への射は同型。
方針：各開でテンソル積の左単位同型の逆を使う。
規約：前層の自然な射そのものが同型であることを示す。
使われ方：KST D4、Toën §3.2 の通常係数の回復。
-/
instance coefficientTensorUnit_self_isIso : IsIso (coefficientTensorUnit A a) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro U
  let := sectionAlgebra a U.unop
  let e := (Algebra.TensorProduct.lid A Γ(X, U.unop)).symm.toRingEquiv.toRingCatIso
  change IsIso e.hom
  infer_instance

/--
概要：H = A のテンソル前層は既に層である。
方針：構造層からの自然同型で層条件を移す。
規約：任意の H のテンソル前層が層であるとは主張しない。
使われ方：KST D4、Toën §3.2 の単位係数の層化比較。
-/
lemma coefficientTensorPresheaf_self_isSheaf :
    Presheaf.IsSheaf (Opens.grothendieckTopology X) (coefficientTensorPresheaf A a) :=
  (Presheaf.isSheaf_of_iso_iff (asIso (coefficientTensorUnit A a))).mp X.ringCatSheaf.property

/--
概要：H = A の場合の層化比較は同型。
方針：層条件を既に満たす前層の層化の単位は同型であることを使う。
規約：一般の係数の場合の大域切断の主張とは区別する。
使われ方：KST D4、Toën §3.2 の通常係数の構造層への同定。
-/
instance tensorCoefficientComparison_self_isIso : IsIso (tensorCoefficientComparison A a) :=
  isIso_toSheafify (Opens.grothendieckTopology X) (coefficientTensorPresheaf_self_isSheaf a)

/--
概要：H = A の具体的係数環層への構造射は同型。
方針：テンソル前層への単位と層化比較の二つの同型を合成する。
規約：環層の射についての同型性を述べる。
使われ方：KST D4、Bondal–van den Bergh Thm 3.1.1 の通常係数への特殊化。
-/
instance tensorCoefficientSheaf_self_structureMap_isIso :
    IsIso (tensorCoefficientSheaf A a).structureMap := by
  have : (sheafToPresheaf (Opens.grothendieckTopology X) RingCat.{u}).ReflectsIsomorphisms :=
    (fullyFaithfulSheafToPresheaf _ _).reflectsIsomorphisms
  have : IsIso ((sheafToPresheaf (Opens.grothendieckTopology X) RingCat.{u}).map
      (tensorCoefficientSheaf A a).structureMap) := by
    have := coefficientTensorUnit_self_isIso a
    have := tensorCoefficientComparison_self_isIso a
    change IsIso (coefficientTensorUnit A a ≫ tensorCoefficientComparison A a)
    infer_instance
  exact isIso_of_reflects_iso (tensorCoefficientSheaf A a).structureMap
    (sheafToPresheaf (Opens.grothendieckTopology X) RingCat.{u})

/--
概要：基礎環を係数とした係数環層と構造層の標準同型。
方針：構成済みの構造射の逆を取る。
規約：構造層の環層としての同型。
使われ方：KST D4、Bondal–van den Bergh Thm 3.1.1、Toën §3.2 の通常の D_qc への接続。
-/
def tensorCoefficientSelfIso : (tensorCoefficientSheaf A a).ring ≅ X.ringCatSheaf :=
  (asIso (tensorCoefficientSheaf A a).structureMap).symm

end SerrePositivity.KST.DerivedGeometry
