module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.KanModels.KanCommSqCone
public import SerrePositivity.KST.Fibration.StrictConeTransformation
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.SpacePullbacks
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.StrictConeReindex
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanAnodyneLocalization
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanInvertible
public import SerrePositivity.KST.Comparison.AlternativeFiberCriterion

/-! # 元の Kan 四角形を、同じ四頂点と全脚を持つ coherent 錐にする -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories

open SerrePositivity.KST.Comparison
open SerrePositivity.SimplicialModel
namespace SerrePositivity.KST.Fibration

variable {P X Y Z : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}}
  {a : P.obj ⟶ X.obj} {b : P.obj ⟶ Y.obj} {f : X.obj ⟶ Z.obj} {g : Y.obj ⟶ Z.obj}

/-- 一脚 fibration の元の四角形の homotopy pullback 比較は同じ厳密比較射で判定できる。 -/
theorem kanCommSqComparison_localized_isIso [Fibration g]
    (sq : CommSq a b f g) (hsq : IsHomotopyPullback sq) :
    IsIso (AnodyneHomotopy.anodyneQ.map (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.KanModels.kanCommSqComparison sq)) := by
  apply (isHomotopyPullback_iff_alternative_fiber sq.flip (𝟙 Y.obj) (by infer_instance)
    g ((SSet.modelCategoryQuillen.fibration_iff _).mp inferInstance) (Category.id_comp g)
    (IsPullback.of_hasPullback g f).flip (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.KanModels.kanCommSqComparison sq) ?_ ?_).mp
  · exact (isHomotopyPullback_flip_iff sq).mpr hsq
  · exact pullback.lift_snd _ _ _
  · simpa only [Category.comp_id, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.KanModels.kanCommSqComparison] using pullback.lift_fst b a sq.w.symm

/-- 一脚 fibration の場合、元の homotopy pullback 四角形は同じ coherent 極限錐になる。 -/
theorem kanCommSqCone_isLimit_of_fibration [Fibration g]
    (sq : CommSq a b f g) (hsq : IsHomotopyPullback sq) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.KanModels.kanCommSqCone sq)) := by
  let q : Y ⟶ Z := g
  let p : X ⟶ Z := f
  let c := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.KanModels.kanCommSqCone sq
  let d := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.kanPullbackCone q p
  let k : c.pt ⟶ d.pt := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.KanModels.kanCommSqComparison sq
  have hk : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge k) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentKanEdge_isInvertible_of_isQCatEquivalence
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.isQCatEquivalence_of_anodyneQ_isIso k (kanCommSqComparison_localized_isIso sq hsq))
  have hi : ∀ j : AsSmall.{u} WalkingCospan,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (𝟙 ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.kanPullbackDiagram q p).obj j))) :=
    fun j => _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.KanModels.kanIdentityEdge_isInvertible _
  apply (strictCoherentCone_isLimit_iff_of_transformation (𝟙 _) c d k ?_ hi hk).mpr
  · exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.coherentConeCast_isLimit_iff _ _).mp (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spacePullbackCone_isLimitCone q p)
  · have hl : k ≫ d.π.app (AsSmall.up.obj WalkingCospan.left) =
        c.π.app (AsSmall.up.obj WalkingCospan.left) := by
      change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.KanModels.kanCommSqComparison sq ≫ (pullback.fst g f ≫ 𝟙 Y.obj) = b
      simp only [Category.comp_id, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.KanModels.kanCommSqComparison, pullback.lift_fst]
    have hr : k ≫ d.π.app (AsSmall.up.obj WalkingCospan.right) =
        c.π.app (AsSmall.up.obj WalkingCospan.right) := by
      change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.KanModels.kanCommSqComparison sq ≫ (pullback.snd g f ≫ 𝟙 X.obj) = a
      simp only [Category.comp_id, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.KanModels.kanCommSqComparison, pullback.lift_snd]
    intro j
    simp only [NatTrans.id_app, Category.comp_id]
    rcases j with ⟨_ | (_ | _)⟩
    · have hd := d.w (AsSmall.up.map WalkingCospan.Hom.inl)
      have hc := c.w (AsSmall.up.map WalkingCospan.Hom.inl)
      exact (congrArg (fun t => k ≫ t) hd.symm).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun t => t ≫ q) hl).trans hc))
    · exact hl
    · exact hr

end SerrePositivity.KST.Fibration
