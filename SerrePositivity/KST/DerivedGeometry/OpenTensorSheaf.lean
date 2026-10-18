module

public import SerrePositivity.KST.DerivedGeometry.OpenTensorPresheaf
public import SerrePositivity.KST.DerivedGeometry.OpenSheafification
public import SerrePositivity.KST.DerivedGeometry.TensorCoefficientSheaf
public import SerrePositivity.KST.DerivedGeometry.CoefficientRestriction

/-!
# 具体的係数環層と開部分への制限

概要：開部分上で直接構成した係数環層を大域係数環層の制限と同定する。
方針：テンソル前層の自然同型と制限・層化の可換性を合成する。
規約：構造層からの射との両立を明示し、導来降下は仮定しない。
使われ方：KST D4、Toën Derived Azumaya §3.2 の局所模型への接続。
-/

@[expose] public section

noncomputable section

set_option maxSynthPendingDepth 8
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace SerrePositivity.KST.DerivedGeometry

variable {A : Type u} [CommRing A] (H : Type u) [Ring H] [Algebra A H]
  {X : Scheme.{u}} (a : A →+* Γ(X, ⊤)) (U : X.Opens)

/--
概要：開部分で直接構成した係数環層と大域構成の制限は環層として同型。
方針：前層の同型を層化し、開制限との層化の比較を合成する。
規約：H の平坦性・可換性を要求しない。
使われ方：KST D4、Toën §3.2 のアフィン局所係数との比較。
-/
def openTensorSheafIso :
    (tensorCoefficientSheaf H (restrictedBaseMap a U)).ring ≅
      (U.sheafRestrict (C := RingCat)).obj (tensorCoefficientSheaf H a).ring :=
  (presheafToSheaf (Opens.grothendieckTopology U.toScheme) RingCat).mapIso
    (openTensorPresheafIso H a U) ≪≫
  openSheafificationIso U.isOpenEmbedding RingCat (coefficientTensorPresheaf H a)

/--
概要：係数環層の開制限の比較は層化前の比較射と可換。
方針：層化の単位の自然性と開制限の層化比較の可換式を使う。
規約：制限の前合成は開像の関手を使う。
使われ方：KST D4、Toën §3.2 の指定された局所比較の計算。
-/
lemma openTensorSheafIso_fac :
    tensorCoefficientComparison H (restrictedBaseMap a U) ≫
      (openTensorSheafIso H a U).hom.hom =
    (openTensorPresheafIso H a U).hom ≫
      Functor.whiskerLeft U.ι.opensFunctor.op (tensorCoefficientComparison H a) := by
  change toSheafify _ _ ≫ sheafifyMap _ (openTensorPresheafIso H a U).hom ≫
      (openSheafificationIso U.isOpenEmbedding RingCat (coefficientTensorPresheaf H a)).hom.hom = _
  rw [← toSheafify_naturality_assoc]
  erw [openSheafificationIso_fac U.isOpenEmbedding RingCat (coefficientTensorPresheaf H a)]
  rfl

/--
概要：係数環層の開制限の同型は構造層からの射と可換。
方針：層化比較の可換式と前層の単位との可換式を合成する。
規約：直接構成と制限による係数構造を指定された射で比較する。
使われ方：KST D4、Toën §3.2 の正則 O 加群の局所比較。
-/
lemma openTensorSheafIso_structureMap :
    (tensorCoefficientSheaf H (restrictedBaseMap a U)).structureMap ≫
      (openTensorSheafIso H a U).hom =
    ((tensorCoefficientSheaf H a).restrict U).structureMap := by
  apply Sheaf.hom_ext
  change coefficientTensorUnit H (restrictedBaseMap a U) ≫
      (tensorCoefficientComparison H (restrictedBaseMap a U) ≫
        (openTensorSheafIso H a U).hom.hom) =
    Functor.whiskerLeft U.ι.opensFunctor.op
      (coefficientTensorUnit H a ≫ tensorCoefficientComparison H a)
  rw [openTensorSheafIso_fac, ← Category.assoc, openTensorPresheafIso_unit,
    Functor.whiskerLeft_comp]

/--
概要：構造射からの係数環層の構成は開部分への制限と可換。
方針：構造射の制限の基礎環写像を展開し、環層の制限同型を使う。
規約：構造射の制限は開部分の包含との合成。
使われ方：KST D4、Toën §3.2 の実際の局所係数環層。
-/
def coefficientSheafOfMorphism_restrictIso (f : X ⟶ Spec (CommRingCat.of A)) :
    (coefficientSheafOfMorphism H (U.ι ≫ f)).ring ≅
      ((coefficientSheafOfMorphism H f).restrict U).ring :=
  openTensorSheafIso H (globalBaseMap f) U

end SerrePositivity.KST.DerivedGeometry
