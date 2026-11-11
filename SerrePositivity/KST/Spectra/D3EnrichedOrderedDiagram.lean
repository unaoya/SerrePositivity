module

public import SerrePositivity.KST.Spectra.EnrichedOrderedCylinderNerve

/-!
概要：全入力 Hom の混合作用から、順序図式上の実豊穣関手を構成する。
方針：元の順序の証明を Hom とともに保持し、単位・合成則を同じ二射影で検証。
規約：具体的な内部 Hom 対象を展開せず、一般豊穣変数の段階で法則を証明する。
使われ方：d3 の実点つきパラメータ図式の共同評価。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
namespace SerrePositivity.KST.Spectra.D3EnrichedOrderedDiagram
open EnrichedOrderedCylinder
variable {J : Type w} [Preorder J] {C : Type v} {D : Type z}
  [EnrichedCategory SSet.{u} C] [EnrichedCategory SSet.{u} D]
  (F : J → EnrichedFunctor SSet.{u} C D)
  (H : ∀ i j : J, i ≤ j → ∀ X Y : C,
    (X ⟶[SSet] Y) ⟶ ((F i).obj X ⟶[SSet] (F j).obj Y))

def obj (X : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedOrderedCylinder.Object J C) : D := (F X.position).obj X.val

def map (X Y : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedOrderedCylinder.Object J C) : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedOrderedCylinder.hom X Y ⟶ (obj F X ⟶[SSet] obj F Y) := by
  classical
  exact if h : X.position ≤ Y.position then snd _ _ ≫ H _ _ h X.val Y.val
    else _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedOrderedCylinder.eliminateHom X Y h _

@[simp]
lemma map_app (X Y : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedOrderedCylinder.Object J C) (d : SimplexCategoryᵒᵖ)
    (p : (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedOrderedCylinder.orderWitness J X.position Y.position : SSet.{u}).obj d)
    (f : (X.val ⟶[SSet] Y.val).obj d) :
    (map F H X Y).app d (p, f) = (H _ _ p.down.down X.val Y.val).app d f := by
  classical
  rw [map, dite_eq_left p.down.down]
  rfl

variable (hi : ∀ (i : J) (X Y : C), H i i le_rfl X Y = (F i).map X Y)
  (hc : ∀ (i j k : J) (h : i ≤ j) (h' : j ≤ k) (X Y Z : C),
    eComp SSet X Y Z ≫ H i k (le_trans h h') X Z =
      (H i j h X Y ⊗ₘ H j k h' Y Z) ≫ eComp SSet ((F i).obj X) ((F j).obj Y) ((F k).obj Z))

include hi in
lemma map_id (X : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedOrderedCylinder.Object J C) : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedOrderedCylinder.identity X ≫ map F H X X = eId SSet (obj F X) := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  rintro ⟨⟩
  change (map F H X X).app d (⟨⟨le_rfl⟩⟩, (eId SSet X.val).app d PUnit.unit) = _
  rw [map_app, hi]
  exact ConcreteCategory.congr_hom (NatTrans.congr_app ((F X.position).map_id X.val) d) PUnit.unit

include hc in
lemma map_comp (X Y Z : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedOrderedCylinder.Object J C) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedOrderedCylinder.composition X Y Z ≫ map F H X Z =
      (map F H X Y ⊗ₘ map F H Y Z) ≫ eComp SSet (obj F X) (obj F Y) (obj F Z) := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  rintro ⟨⟨p, f⟩, ⟨q, g⟩⟩
  change (map F H X Z).app d
    (⟨⟨le_trans p.down.down q.down.down⟩⟩, (eComp SSet X.val Y.val Z.val).app d (f, g)) = _
  rw [map_app]
  change (H _ _ (le_trans p.down.down q.down.down) X.val Z.val).app d
    ((eComp SSet X.val Y.val Z.val).app d (f, g)) =
      (eComp SSet (obj F X) (obj F Y) (obj F Z)).app d
        ((map F H X Y).app d (p, f), (map F H Y Z).app d (q, g))
  rw [map_app, map_app]
  let fg : ((X.val ⟶[SSet] Y.val) ⊗ (Y.val ⟶[SSet] Z.val)).obj d := (f, g)
  exact ConcreteCategory.congr_hom (NatTrans.congr_app
    (hc _ _ _ p.down.down q.down.down X.val Y.val Z.val) d) fg

include hi hc in
def functor : EnrichedFunctor SSet.{u} (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedOrderedCylinder.Object J C) D where
  obj := obj F
  map := map F H
  map_id := map_id F H hi
  map_comp := map_comp F H hc

lemma stage (i : J) :
    (stageInclusion (C := C) i).comp SSet (functor F H hi hc) = F i := by
  apply EnrichedFunctor.ext SSet
  case h_obj => intro X; rfl
  intro X Y
  simp only [eqToHom_refl, Category.comp_id]
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro f
  change (map F H (⟨i, X⟩ : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedOrderedCylinder.Object J C) (⟨i, Y⟩ : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedOrderedCylinder.Object J C)).app d (⟨⟨le_rfl⟩⟩, f) = _
  rw [map_app, hi]
  rfl

end SerrePositivity.KST.Spectra.D3EnrichedOrderedDiagram
