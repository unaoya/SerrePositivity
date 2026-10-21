module

public import SerrePositivity.EInfinity.Hammock.FixedObjectCategoryAugmentation
public import SerrePositivity.EInfinity.Hammock.ColimitGraph

/-!
# 元の相対 augmentation による固定対象の hammock 図式の比較

概要：全語の固定対象の図式から、元の hammock 余極限への自然な augmentation を得る。
方針：元の圏値の比較を nerve・二方向の交換・余極限へ移す。
規約：定数図式への比較も元の全作用素で検証する。
使われ方：自由相対解像の対角 hammock から元の hammock への左比較。
-/

@[expose] public section
universe u uI vI
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.FixedObjectDiagram
open CategoryTheory CategoryTheory.Limits SimplicialLocalization

variable {I : Type uI} [Category.{vI} I] (D : I ⥤ RelativeCategory.{u}) (C : RelativeCategory.{u})
  (p : (i : I) → C.category → (D.obj i).category)
  (hp : ∀ {i j : I} (θ : i ⟶ j) (X : C.category), (D.map θ).functor.obj (p i X) = p j X)
  (A : D ⟶ (Functor.const I).obj C)
  (ha : ∀ i X, (A.app i).functor.obj (p i X) = X)

def graphWordTarget (X Y : C.category) : Word ⥤ I ⥤ SSet.{u} :=
  (Hammock.categoryDiagram C.weakEquivalences X Y ⋙ Functor.const I) ⋙
    (CategoryTheory.Functor.whiskeringRight
      (C := I) (D := Cat.{u, u}) (E := SSet.{u})).obj nerveFunctor

lemma graphWordTarget_flip (X Y : C.category) : (graphWordTarget (I := I) C X Y).flip =
    (Functor.const I).obj (Hammock.graphDiagram C.weakEquivalences X Y) := by
  apply CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro i j θ
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

def graphWordAugmentation (X Y : C.category) : graphWordDiagram D p hp X Y ⟶
    graphWordTarget (I := I) C X Y :=
  Functor.whiskerRight (categoryWordAugmentation D C p hp A ha X Y)
    ((CategoryTheory.Functor.whiskeringRight
      (C := I) (D := Cat.{u, u}) (E := SSet.{u})).obj nerveFunctor)

def graphAugmentation (X Y : C.category) : (graphWordDiagram D p hp X Y).flip ⟶
    (Functor.const I).obj (Hammock.graphDiagram C.weakEquivalences X Y) :=
  (flipFunctor Word I SSet.{u}).map (graphWordAugmentation D C p hp A ha X Y) ≫
    eqToHom (graphWordTarget_flip (I := I) C X Y)

def hammockAugmentation (X Y : C.category) : (graphWordDiagram D p hp X Y).flip ⋙ colim ⟶
    (Functor.const I).obj (colimitGraph C.weakEquivalences X Y) :=
  Functor.whiskerRight (graphAugmentation D C p hp A ha X Y) colim ≫
    (Functor.constComp I (Hammock.graphDiagram C.weakEquivalences X Y) colim).hom

end SerrePositivity.EInfinity.Hammock.FixedObjectDiagram
