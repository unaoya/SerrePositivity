module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.FullColimitReflection
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.FullZeroObject
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.ExactFunctor
/-!
概要：充満 dg 部分圏への実関手の完全性を、周囲への包含後の完全性から反映する。
方針：実零頂点と実余極限の境界充填を全包含で反映する。
規約：部分圏の replete 性を要求しない。使われ方：β5 の射影的模型上の tensor 関手。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
/-- 充満 dg 部分圏への関手は、周囲への包含との合成が完全なら完全。 -/
lemma isExactFunctor_of_postcomp_dgFullInclusion (R : Type u) [CommRing R] (E : Type v)
    [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] (P : E → Prop) {X : SSet.{max u v}}
    (F : X ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (DGFullSubcategory E P))
    [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgFullSubcategoryInclusion R E P))] : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor F where
  preservesZero z hz := by
    have h := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesZero
      (F := F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgFullSubcategoryInclusion R E P)) z hz
    exact ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.isInitialVertex_of_fullInclusion R E P _ h.1,
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.isTerminalVertex_of_fullInclusion R E P _ h.2⟩
  preservesCofiber t ht := by
    apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.isColimitCone_of_fullInclusion R E P (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutCocone _)
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesCofiber
      (F := F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgFullSubcategoryInclusion R E P)) t ht
end SerrePositivity.InfinityCategories.Project.DerivedCategories
