module

public import SerrePositivity.KST.DerivedGeometry.OpenImmersionTensorPresheaf
public import SerrePositivity.KST.DerivedGeometry.CoefficientOpenImmersion
public import SerrePositivity.KST.DerivedGeometry.OpenSheafification
public import SerrePositivity.KST.DerivedGeometry.TensorCoefficientSheaf

/-!
# 開埋め込みに沿う具体的係数環層の比較

概要：開埋め込みの始域で直接構成した係数環層と終域の係数環層の制限を比較する。
方針：係数前層の同型を層化し、制限との層化の可換性を使う。
規約：構造層射との両立を同時に示す。
使われ方：KST D4、Toën Derived Azumaya §3.2 のアフィン同型への輸送。
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
  {X Y : Scheme.{u}} (a : A →+* Γ(Y, ⊤)) (f : X ⟶ Y) [IsOpenImmersion f]

/--
概要：開埋め込みに沿い、係数環層の直接構成と制限を同型で比較する。
方針：前層の同型を層化し、開埋め込みの層化比較と合成する。
規約：H の可換性・平坦性は不要。
使われ方：KST D4、Toën §3.2 のアフィン同型に沿う係数層の輸送。
-/
def openImmersionTensorSheafIso :
    (tensorCoefficientSheaf H (pullbackBaseMap a f)).ring ≅
      ((tensorCoefficientSheaf H a).restrictAlong f).ring :=
  (presheafToSheaf (Opens.grothendieckTopology X) RingCat).mapIso
    (openImmersionTensorPresheafIso H a f) ≪≫
  openSheafificationIso f.isOpenEmbedding RingCat (coefficientTensorPresheaf H a)

/--
概要：開埋め込みの係数環層の比較は指定された層化の比較射と可換。
方針：層化の単位の自然性と開埋め込みの層化比較の単位式を使う。
規約：開像への前合成で制限した比較射を使う。
使われ方：KST D4、Toën §3.2 の構造射との両立の証明。
-/
lemma openImmersionTensorSheafIso_fac :
    tensorCoefficientComparison H (pullbackBaseMap a f) ≫
      (openImmersionTensorSheafIso H a f).hom.hom =
    (openImmersionTensorPresheafIso H a f).hom ≫
      Functor.whiskerLeft f.opensFunctor.op (tensorCoefficientComparison H a) := by
  change toSheafify _ _ ≫ sheafifyMap _ (openImmersionTensorPresheafIso H a f).hom ≫
    (openSheafificationIso f.isOpenEmbedding RingCat (coefficientTensorPresheaf H a)).hom.hom = _
  rw [← toSheafify_naturality_assoc]
  erw [openSheafificationIso_fac f.isOpenEmbedding RingCat (coefficientTensorPresheaf H a)]
  rfl

/--
概要：開埋め込みの係数環層の同型は構造層からの射を保つ。
方針：前層の単位と層化の比較の二つの可換式を合成する。
規約：appIso の逆による構造層の輸送を含む。
使われ方：KST D4、Toën §3.2 の正則 O 加群の比較。
-/
lemma openImmersionTensorSheafIso_structureMap :
    (tensorCoefficientSheaf H (pullbackBaseMap a f)).structureMap ≫
      (openImmersionTensorSheafIso H a f).hom =
    ((tensorCoefficientSheaf H a).restrictAlong f).structureMap := by
  apply Sheaf.hom_ext
  change coefficientTensorUnit H (pullbackBaseMap a f) ≫
      (tensorCoefficientComparison H (pullbackBaseMap a f) ≫
        (openImmersionTensorSheafIso H a f).hom.hom) =
    openImmersionStructureMap f ≫ Functor.whiskerLeft f.opensFunctor.op
      (coefficientTensorUnit H a ≫ tensorCoefficientComparison H a)
  rw [openImmersionTensorSheafIso_fac, ← Category.assoc,
    openImmersionTensorPresheafIso_unit, Category.assoc, Functor.whiskerLeft_comp]

end SerrePositivity.KST.DerivedGeometry
