module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoofPrefixHomotopy
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
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Prefix
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.InfinityCategories
variable {C I : Type u} [Category.{u} C] [Category.{u} I]
  (W : MorphismProperty C) [W.IsMultiplicative] (U : I ⥤ C) {X Y : C}
  (p : U ⟶ (Functor.const I).obj X) (hp : ∀ i, W (p.app i))
  (σ : U ⟶ (Functor.const I).obj Y)
  (hU : ∀ {i j} (a : i ⟶ j), W (U.map a)) (i : I)

def restrictedRoofMap : nerve (Under i) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W X Y :=
  _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Precompose.SameUniverse.diagramColimitMap W
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoof.diagram W (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Prefix.restrictedFrame U i) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Prefix.restrictedAugmentation U p i)
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Prefix.restrictedAugmentation_weak W U p hp i) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Prefix.restrictedRightLeg U σ i)
      (fun f => _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Prefix.restrictedFrame_map_weak W U hU i f))

def constantRoofMap : nerve (Under i) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W (U.obj i) Y :=
  _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Precompose.SameUniverse.diagramColimitMap W
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoof.diagram W (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Prefix.fixedSource U i) (𝟙 _) (fun _ => W.id_mem (U.obj i))
      ((Functor.const (Under i)).map (σ.app i)) (fun f => _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Prefix.fixedSource_map_weak W U i f))

lemma upperMap_eq :
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Precompose.SameUniverse.diagramColimitMap W (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Prefix.upperDiagram W U σ hU i) =
      _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Prefix.constantRoofMap W U σ i := by
  unfold _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Prefix.constantRoofMap
  rw [← _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Prefix.right_triangle U σ i]
  dsimp only [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Prefix.upperDiagram]
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.upperOriginalDiagram_insert,
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Precompose.SameUniverse.diagramColimitMap_wordAction,
    ← _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.upperOriginalDiagram_collapse,
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Precompose.SameUniverse.diagramColimitMap_wordAction]
  exact fun f => _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Prefix.restrictedFrame_map_weak W U hU i f

lemma lowerMap_eq :
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Precompose.SameUniverse.diagramColimitMap W (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Prefix.lowerDiagram W U p hp σ hU i) =
      _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Prefix.restrictedRoofMap W U p hp σ hU i ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.precomposePointMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap W (p.app i)) Y := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Prefix.lowerDiagram, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Prefix.restrictedRoofMap]
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lowerDiagram_insert, ← CategoryTheory.Functor.assoc,
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Precompose.SameUniverse.diagramColimitMap_wordAction,
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Precompose.SameUniverse.diagramColimitMap_precompose]
  exact fun f => _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Prefix.restrictedFrame_map_weak W U hU i f

def normalizedHomotopy : SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Prefix.constantRoofMap W U σ i)
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Prefix.restrictedRoofMap W U p hp σ hU i ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.precomposePointMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap W (p.app i)) Y) :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHomotopyRetarget (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Prefix.colimitHomotopy W U p hp σ hU i)
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Prefix.upperMap_eq W U σ hU i) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Prefix.lowerMap_eq W U p hp σ hU i)

lemma normalizedHomotopy_h : (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Prefix.normalizedHomotopy W U p hp σ hU i).h =
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Prefix.graphHomotopy W U p hp σ hU i).h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion W (U.obj i) Y _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoofPrecomposeWords.word := rfl

lemma constantRoofMap_eq_rightArrow : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Prefix.constantRoofMap W U σ i =
    (CartesianMonoidalCategory.toUnit (nerve (Under i)) : nerve (Under i) ⟶ 𝟙_ SSet.{u}) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap W (σ.app i) := by
  let R := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoof.obj W (𝟙 (U.obj i)) (W.id_mem (U.obj i)) (σ.app i)
  have hF : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoof.diagram W (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Prefix.fixedSource U i) (𝟙 _) (fun _ => W.id_mem (U.obj i))
      ((Functor.const (Under i)).map (σ.app i)) (fun f => _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Prefix.fixedSource_map_weak W U i f) =
      (Functor.const (Under i)).obj R := by
    refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
    intro s t f
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.hom_ext
    intro j
    change Fin 3 at j
    fin_cases j <;> rfl
  have hc : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Precompose.SameUniverse.diagramColimitMap W ((Functor.const (Under i)).obj R) =
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
  unfold _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Prefix.constantRoofMap
  rw [hF, hc, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitRowMap_leftIdentity]

def arrowHomotopy : SSet.Homotopy
    ((CartesianMonoidalCategory.toUnit (nerve (Under i)) : nerve (Under i) ⟶ 𝟙_ SSet.{u}) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap W (σ.app i))
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Prefix.restrictedRoofMap W U p hp σ hU i ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.precomposePointMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap W (p.app i)) Y) :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHomotopyRetarget (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Prefix.normalizedHomotopy W U p hp σ hU i)
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Prefix.constantRoofMap_eq_rightArrow W U σ i) rfl

lemma arrowHomotopy_h : (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Prefix.arrowHomotopy W U p hp σ hU i).h =
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Prefix.graphHomotopy W U p hp σ hU i).h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion W (U.obj i) Y _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoofPrecomposeWords.word := rfl

lemma restrictedRoofMap_eq_precomp : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Prefix.restrictedRoofMap W U p hp σ hU i =
    nerveMap (Under.forget i) ≫ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Precompose.SameUniverse.diagramColimitMap W
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoof.diagram W U p hp σ hU) := by
  have hF : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoof.diagram W (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Prefix.restrictedFrame U i) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Prefix.restrictedAugmentation U p i)
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Prefix.restrictedAugmentation_weak W U p hp i) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Prefix.restrictedRightLeg U σ i)
      (fun f => _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Prefix.restrictedFrame_map_weak W U hU i f) =
      Under.forget i ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoof.diagram W U p hp σ hU := by
    refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
    intro s t f
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.hom_ext
    intro j
    change Fin 3 at j
    fin_cases j <;> rfl
  unfold _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Prefix.restrictedRoofMap
  rw [hF]
  rfl

lemma restrictedRoofMap_underMap {j : I} (a : i ⟶ j) :
    nerveMap (Under.map a) ≫ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Prefix.restrictedRoofMap W U p hp σ hU i =
      _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Prefix.restrictedRoofMap W U p hp σ hU j := by
  have h : nerveMap (Under.map a) ≫ nerveMap (Under.forget i) =
      nerveMap (Under.forget j) := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro τ
    rfl
  rw [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Prefix.restrictedRoofMap_eq_precomp, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Prefix.restrictedRoofMap_eq_precomp, ← Category.assoc, h]

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Prefix
