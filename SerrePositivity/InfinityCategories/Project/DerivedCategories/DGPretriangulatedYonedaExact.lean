module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGRepleteYonedaStability
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModulePropertyExactInclusion

/-! # 前三角 dg 圏の実 Yoneda の完全性と押し出しの反映

概要：共通宇宙の Yoneda は完全であり、実押し出し四角形を反映する。
方針：ホモトピー表現可能部分への同値と全加群への充満包含を使う。
規約：実余極限性を反映する。使われ方：dg 関手の完全性の加群模型による判定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory MonoidalCategory DifferentialGraded
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v)
  [DGCategory A D] [Small.{u} D] [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D]

/-- 共通宇宙の前三角 dg 圏から全加群への実 Yoneda は完全。 -/
theorem dgPretriangulatedYoneda_isExactFunctor :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown.{u, v, max (u + 1) v} A D).comp (dgYoneda A D))) := by
  let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRepleteYonedaNerve_isExactFunctor A D
  let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRepleteRepresentablesInclusion_isExactFunctor A D
  have h : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRepleteYoneda A D) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgFullSubcategoryInclusion A (RightModule A D)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomotopyRepresentable A D))) := inferInstance
  rwa [← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRepleteYoneda_inclusion] at h

/-- 前三角 dg 圏の共通宇宙の実 Yoneda は、全四角形の押し出し性を反映する。 -/
lemma dgPretriangulatedYoneda_reflectsPushoutSquare
    (L : (Δ[1] ⊗ Δ[1] : SSet.{max (u + 1) v}) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{v, max (u + 1) v} D))
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (L ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown A D).comp (dgYoneda A D)))) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare L := by
  let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftNerve_isStable A D
  let : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGRepleteRepresentables A D)) :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomotopyRepresentableNerve_isStable A D
  let R := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRepleteYoneda A D)
  let I := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgFullSubcategoryInclusion A (RightModule A D)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomotopyRepresentable A D))
  have he : R ≫ I = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown A D).comp (dgYoneda A D)) := by
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRepleteYoneda_inclusion]
  have hr : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (L ≫ R) := by
    apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.isColimitCone_of_fullInclusion A (RightModule A D)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomotopyRepresentable A D) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutCocone _)
    change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare ((L ≫ R) ≫ I)
    rwa [Category.assoc, he]
  have hp := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable.pullback_of_pushout_square (L ≫ R) hr
  have hl : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare L := by
    apply ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRepleteYonedaNerveEquivalence A D).isLimitCone_iff (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone L)).mpr
    simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone,
      Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRepleteYonedaNerveEquivalence_hom] using hp
  exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable.pushout_of_pullback_square L hl

end SerrePositivity.InfinityCategories.Project.DerivedCategories
