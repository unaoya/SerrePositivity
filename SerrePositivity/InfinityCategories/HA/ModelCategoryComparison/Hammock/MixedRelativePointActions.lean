module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MixedRelativeComposition
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.ReducedPointActions

/-!
# 異なる Hom の宇宙を持つ相対関手と元の前後合成

概要：元の一列の点とそれによる前後合成を元の相対関手で回収する。
方針：二頂点と全単体を照合し、元の合成保存を適用する。
規約：生の元の射・全単体・同じ reduced 同型を保持する。
使われ方：cofibrant 包含の作用と実 DK/Map^h 比較の接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MixedRelative
open _root_.CategoryTheory
variable {C D : Type (u + 1)} [Category.{u + 1} C] [Category.{u} D]
  {W : MorphismProperty C} [W.IsMultiplicative] {V : MorphismProperty D} [V.IsMultiplicative]
  (F : LocalizerMorphism W V) {X Y Z : C}

omit [W.IsMultiplicative] [V.IsMultiplicative] in
lemma forward_obj (p : X ⟶ Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeZigzagFunctor.obj F (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzag.obj (W := W) p) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzag.obj (W := V) (F.functor.map p) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagExt.object_ext
  · intro j
    change Fin 2 at j
    cases j using Fin.cases with
    | zero => rfl
    | succ j => rfl
  · intro j
    change Fin 1 at j
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    rfl

lemma arrowSimplex_map (p : X ⟶ Y) (n : SimplexCategoryᵒᵖ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowSimplex W p n ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeZigzagFunctor.functor F = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowSimplex V (F.functor.map p) n := by
  apply CategoryTheory.Functor.hext (fun _ => _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MixedRelative.forward_obj F p)
  intro d e f
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagExt.hom_hext (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MixedRelative.forward_obj F p) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MixedRelative.forward_obj F p)
  intro j
  change Fin 2 at j
  cases j using Fin.cases with
  | zero => exact heq_of_eq (F.functor.map_id _)
  | succ j => exact heq_of_eq (F.functor.map_id _)

lemma arrowPoint_map (p : X ⟶ Y) (n : SimplexCategoryᵒᵖ) :
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MixedRelative.colimitMap F X Y).app n (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowPoint W p n) = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowPoint V (F.functor.map p) n :=
  (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MixedRelative.graphInclusion_point F (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowSimplex W p n)).trans
    (congrArg (fun H => (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion V (F.functor.obj X) (F.functor.obj Y)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward)).app n H) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MixedRelative.arrowSimplex_map F p n))

lemma colimitMap_postcompose (X : C) (g : Y ⟶ Z) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.postcomposePointMap X (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap W g) ≫ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MixedRelative.colimitMap F X Z =
      _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MixedRelative.colimitMap F X Y ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.postcomposePointMap (F.functor.obj X) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap V (F.functor.map g)) := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro p
  change (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MixedRelative.colimitMap F X Z).app n (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.composePoint W X Y Z p (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowPoint W g n)) = _
  rw [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MixedRelative.composePoint_map, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MixedRelative.arrowPoint_map]
  rfl

lemma colimitMap_precompose (Z : C) (f : X ⟶ Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.precomposePointMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap W f) Z ≫ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MixedRelative.colimitMap F X Z =
      _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MixedRelative.colimitMap F Y Z ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.precomposePointMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap V (F.functor.map f)) (F.functor.obj Z) := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro p
  change (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MixedRelative.colimitMap F X Z).app n (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.composePoint W X Y Z (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowPoint W f n) p) = _
  rw [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MixedRelative.composePoint_map, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MixedRelative.arrowPoint_map]
  rfl

lemma reducedMap_postcompose (X : C) (g : Y ⟶ Z) :
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.reducedPostcomposeMap W X g ≫ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MixedRelative.reducedMap F X Z =
      _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MixedRelative.reducedMap F X Y ≫ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.reducedPostcomposeMap V (F.functor.obj X) (F.functor.map g) := by
  apply (cancel_epi (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.reducedColimitIso W X Y).hom).1
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.reducedColimitIso_postcompose, Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MixedRelative.reducedColimitIso_map,
    ← Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MixedRelative.colimitMap_postcompose, Category.assoc]
  symm
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MixedRelative.reducedColimitIso_map, Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.reducedColimitIso_postcompose]

lemma reducedMap_precompose (Z : C) (f : X ⟶ Y) :
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.reducedPrecomposeMap W Z f ≫ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MixedRelative.reducedMap F X Z =
      _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MixedRelative.reducedMap F Y Z ≫ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.reducedPrecomposeMap V (F.functor.obj Z) (F.functor.map f) := by
  apply (cancel_epi (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.reducedColimitIso W Y Z).hom).1
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.reducedColimitIso_precompose, Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MixedRelative.reducedColimitIso_map,
    ← Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MixedRelative.colimitMap_precompose, Category.assoc]
  symm
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MixedRelative.reducedColimitIso_map, Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.reducedColimitIso_precompose]

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MixedRelative
