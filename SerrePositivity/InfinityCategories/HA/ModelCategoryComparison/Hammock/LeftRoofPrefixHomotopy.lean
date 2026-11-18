module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoofSameUniverseComparison
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import SerrePositivity.HomotopicalAlgebra.Simplicial.HomotopyClasses

/-!
# 元の roof の始点を固定した Under 全図式の四列円柱

概要：始点 i からの全射 i→j を保ち、元の右脚と p_i による前合成の全円柱を作る。
方針：元の自然性の二つの三角形を既存の四列図式へ代入する。
規約：Under の全射・全作用素・元の弱同値を保持する。
使われ方：native roof の全合成 prism の各始点からの Hom 写像。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Prefix
open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.SimplicialModel
variable {C I : Type u} [Category.{u} C] [Category.{u} I]
  (W : MorphismProperty C) [W.IsMultiplicative] (U : I ⥤ C) {X Y : C}
  (p : U ⟶ (Functor.const I).obj X) (hp : ∀ i, W (p.app i))
  (σ : U ⟶ (Functor.const I).obj Y)
  (hU : ∀ {i j} (a : i ⟶ j), W (U.map a)) (i : I)

abbrev restrictedFrame : Under i ⥤ C := Under.forget i ⋙ U
abbrev fixedSource : Under i ⥤ C := (Functor.const (Under i)).obj (U.obj i)

def inclusion : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Prefix.fixedSource U i ⟶ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Prefix.restrictedFrame U i where
  app s := U.map s.hom
  naturality {_s _t} f := by
    change 𝟙 _ ≫ U.map _ = U.map _ ≫ U.map f.right
    rw [Category.id_comp, ← U.map_comp, Under.w]

def restrictedAugmentation : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Prefix.restrictedFrame U i ⟶ (Functor.const (Under i)).obj X :=
  Functor.whiskerLeft (Under.forget i) p

def restrictedRightLeg : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Prefix.restrictedFrame U i ⟶ (Functor.const (Under i)).obj Y :=
  Functor.whiskerLeft (Under.forget i) σ

lemma augmentation_triangle : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Prefix.inclusion U i ≫ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Prefix.restrictedAugmentation U p i =
    (Functor.const (Under i)).map (p.app i) := by
  apply NatTrans.ext
  funext s
  exact (p.naturality s.hom).trans (Category.comp_id _)

lemma right_triangle : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Prefix.inclusion U i ≫ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Prefix.restrictedRightLeg U σ i =
    (Functor.const (Under i)).map (σ.app i) := by
  apply NatTrans.ext
  funext s
  exact (σ.naturality s.hom).trans (Category.comp_id _)

include hp in
omit [W.IsMultiplicative] in
lemma restrictedAugmentation_weak (s : Under i) : W ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Prefix.restrictedAugmentation U p i).app s) :=
  hp s.right

include hU in
omit [W.IsMultiplicative] in
lemma restrictedFrame_map_weak {s t : Under i} (f : s ⟶ t) :
    W ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Prefix.restrictedFrame U i).map f) := hU f.right

lemma fixedSource_map_weak {s t : Under i} (f : s ⟶ t) :
    W ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Prefix.fixedSource U i).map f) := W.id_mem (U.obj i)

def upperDiagram : Under i ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoofPrecomposeWords.word (U.obj i) Y :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.upperDiagram W (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Prefix.fixedSource U i) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Prefix.restrictedFrame U i) (𝟙 _)
    (fun _ => W.id_mem (U.obj i)) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Prefix.inclusion U i) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Prefix.restrictedRightLeg U σ i)
    (fun f => _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Prefix.fixedSource_map_weak W U i f) (fun f => _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Prefix.restrictedFrame_map_weak W U hU i f)

def lowerDiagram : Under i ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoofPrecomposeWords.word (U.obj i) Y :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lowerDiagram W (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Prefix.restrictedFrame U i) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Prefix.restrictedAugmentation U p i)
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Prefix.restrictedAugmentation_weak W U p hp i) (p.app i) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Prefix.restrictedRightLeg U σ i)
    (fun f => _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Prefix.restrictedFrame_map_weak W U hU i f)

def graphHomotopy : SSet.Homotopy
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Precompose.SameUniverse.diagramGraphMap W (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Prefix.upperDiagram W U σ hU i))
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Precompose.SameUniverse.diagramGraphMap W (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Prefix.lowerDiagram W U p hp σ hU i)) := by
  apply _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Precompose.SameUniverse.diagramHomotopy W (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Prefix.fixedSource U i) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Prefix.restrictedFrame U i)
    (𝟙 _) (fun _ => W.id_mem (U.obj i)) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Prefix.restrictedAugmentation U p i)
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Prefix.restrictedAugmentation_weak W U p hp i) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Prefix.inclusion U i) (p.app i)
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Prefix.restrictedRightLeg U σ i) _ (fun f => _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Prefix.fixedSource_map_weak W U i f)
    (fun f => _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Prefix.restrictedFrame_map_weak W U hU i f)
  rw [Category.id_comp]
  exact _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Prefix.augmentation_triangle U p i

def colimitHomotopy : SSet.Homotopy
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Precompose.SameUniverse.diagramColimitMap W (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Prefix.upperDiagram W U σ hU i))
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Precompose.SameUniverse.diagramColimitMap W (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Prefix.lowerDiagram W U p hp σ hU i)) :=
  HomotopyClasses.postHomotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion W (U.obj i) Y _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoofPrecomposeWords.word)
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Prefix.graphHomotopy W U p hp σ hU i)

lemma inclusion_underMap {j : I} (a : i ⟶ j) :
    Functor.whiskerLeft (Under.map a) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Prefix.inclusion U i) =
      (Functor.const (Under j)).map (U.map a) ≫ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Prefix.inclusion U j := by
  apply NatTrans.ext
  funext s
  exact U.map_comp a s.hom

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Prefix
