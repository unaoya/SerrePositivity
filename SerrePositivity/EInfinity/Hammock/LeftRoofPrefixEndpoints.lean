module

public import SerrePositivity.EInfinity.Hammock.LeftRoofPrefixHomotopy
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoofLeftIdentity
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SpanHomotopyGluing

/-!
# 元の Under 四列円柱の同じ右脚と前合成 roof への両端回収

概要：全円柱を変更せず、上端を恒等左脚の roof、下端を p_i による元の前合成へ戻す。
方針：元の語の挿入・縮約と自然性の三角形を厳密に使う。
規約：Under の全パラメータを保ち、局所化内の等式だけで円柱を代用しない。
使われ方：native roof の全 coherent 合成 prism の Hom 写像。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.Hammock.LeftRoof.Prefix
open CategoryTheory Limits MonoidalCategory
open SerrePositivity.InfinityCategories
variable {C I : Type u} [Category.{u} C] [Category.{u} I]
  (W : MorphismProperty C) [W.IsMultiplicative] (U : I ⥤ C) {X Y : C}
  (p : U ⟶ (Functor.const I).obj X) (hp : ∀ i, W (p.app i))
  (σ : U ⟶ (Functor.const I).obj Y)
  (hU : ∀ {i j} (a : i ⟶ j), W (U.map a)) (i : I)

def restrictedRoofMap : nerve (Under i) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W X Y :=
  Precompose.SameUniverse.diagramColimitMap W
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoof.diagram W (restrictedFrame U i) (restrictedAugmentation U p i)
      (restrictedAugmentation_weak W U p hp i) (restrictedRightLeg U σ i)
      (fun f => restrictedFrame_map_weak W U hU i f))

def constantRoofMap : nerve (Under i) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W (U.obj i) Y :=
  Precompose.SameUniverse.diagramColimitMap W
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoof.diagram W (fixedSource U i) (𝟙 _) (fun _ => W.id_mem (U.obj i))
      ((Functor.const (Under i)).map (σ.app i)) (fun f => fixedSource_map_weak W U i f))

lemma upperMap_eq :
    Precompose.SameUniverse.diagramColimitMap W (upperDiagram W U σ hU i) =
      constantRoofMap W U σ i := by
  unfold constantRoofMap
  rw [← right_triangle U σ i]
  dsimp only [upperDiagram]
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.upperOriginalDiagram_insert,
    Precompose.SameUniverse.diagramColimitMap_wordAction,
    ← _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.upperOriginalDiagram_collapse,
    Precompose.SameUniverse.diagramColimitMap_wordAction]
  exact fun f => restrictedFrame_map_weak W U hU i f

lemma lowerMap_eq :
    Precompose.SameUniverse.diagramColimitMap W (lowerDiagram W U p hp σ hU i) =
      restrictedRoofMap W U p hp σ hU i ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.precomposePointMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap W (p.app i)) Y := by
  dsimp only [lowerDiagram, restrictedRoofMap]
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lowerDiagram_insert, ← CategoryTheory.Functor.assoc,
    Precompose.SameUniverse.diagramColimitMap_wordAction,
    Precompose.SameUniverse.diagramColimitMap_precompose]
  exact fun f => restrictedFrame_map_weak W U hU i f

def normalizedHomotopy : SSet.Homotopy (constantRoofMap W U σ i)
    (restrictedRoofMap W U p hp σ hU i ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.precomposePointMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap W (p.app i)) Y) :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHomotopyRetarget (colimitHomotopy W U p hp σ hU i)
    (upperMap_eq W U σ hU i) (lowerMap_eq W U p hp σ hU i)

lemma normalizedHomotopy_h : (normalizedHomotopy W U p hp σ hU i).h =
    (graphHomotopy W U p hp σ hU i).h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion W (U.obj i) Y _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoofPrecomposeWords.word := rfl

lemma constantRoofMap_eq_rightArrow : constantRoofMap W U σ i =
    (CartesianMonoidalCategory.toUnit (nerve (Under i)) : nerve (Under i) ⟶ 𝟙_ SSet.{u}) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap W (σ.app i) := by
  let R := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoof.obj W (𝟙 (U.obj i)) (W.id_mem (U.obj i)) (σ.app i)
  have hF : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoof.diagram W (fixedSource U i) (𝟙 _) (fun _ => W.id_mem (U.obj i))
      ((Functor.const (Under i)).map (σ.app i)) (fun f => fixedSource_map_weak W U i f) =
      (Functor.const (Under i)).obj R := by
    refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
    intro s t f
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.hom_ext
    intro j
    change Fin 3 at j
    fin_cases j <;> rfl
  have hc : Precompose.SameUniverse.diagramColimitMap W ((Functor.const (Under i)).obj R) =
      (CartesianMonoidalCategory.toUnit (nerve (Under i)) : nerve (Under i) ⟶ 𝟙_ SSet.{u}) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitRowMap R := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro a
    apply congrArg ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion W (U.obj i) Y _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoof.word).app n)
    refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
    intro s t f
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl
  unfold constantRoofMap
  rw [hF, hc, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitRowMap_leftIdentity]

def arrowHomotopy : SSet.Homotopy
    ((CartesianMonoidalCategory.toUnit (nerve (Under i)) : nerve (Under i) ⟶ 𝟙_ SSet.{u}) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap W (σ.app i))
    (restrictedRoofMap W U p hp σ hU i ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.precomposePointMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap W (p.app i)) Y) :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHomotopyRetarget (normalizedHomotopy W U p hp σ hU i)
    (constantRoofMap_eq_rightArrow W U σ i) rfl

lemma arrowHomotopy_h : (arrowHomotopy W U p hp σ hU i).h =
    (graphHomotopy W U p hp σ hU i).h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion W (U.obj i) Y _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoofPrecomposeWords.word := rfl

lemma restrictedRoofMap_eq_precomp : restrictedRoofMap W U p hp σ hU i =
    nerveMap (Under.forget i) ≫ Precompose.SameUniverse.diagramColimitMap W
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoof.diagram W U p hp σ hU) := by
  have hF : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoof.diagram W (restrictedFrame U i) (restrictedAugmentation U p i)
      (restrictedAugmentation_weak W U p hp i) (restrictedRightLeg U σ i)
      (fun f => restrictedFrame_map_weak W U hU i f) =
      Under.forget i ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoof.diagram W U p hp σ hU := by
    refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
    intro s t f
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.hom_ext
    intro j
    change Fin 3 at j
    fin_cases j <;> rfl
  unfold restrictedRoofMap
  rw [hF]
  rfl

lemma restrictedRoofMap_underMap {j : I} (a : i ⟶ j) :
    nerveMap (Under.map a) ≫ restrictedRoofMap W U p hp σ hU i =
      restrictedRoofMap W U p hp σ hU j := by
  have h : nerveMap (Under.map a) ≫ nerveMap (Under.forget i) =
      nerveMap (Under.forget j) := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro τ
    rfl
  rw [restrictedRoofMap_eq_precomp, restrictedRoofMap_eq_precomp, ← Category.assoc, h]

end SerrePositivity.EInfinity.Hammock.LeftRoof.Prefix
