module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.Resolutions.DGSemifreeModules
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Actions.DGModuleClosedPropertyStability
public import SerrePositivity.DifferentialGraded.Derived.Basic
/-!
概要：全 Hom end の意味で射影的な右 dg 加群の安定な実 nerve。
方針：零・cone・shift の実閉性から標準四角形を制限する。
規約：元の dg 圏の Hom の平坦性を仮定しない。使われ方：β5 の半自由模型との比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory MonoidalCategory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
/-- 全 Hom end による射影的加群の実対象条件。 -/
def dgModuleProjectiveProperty (M : _root_.SerrePositivity.DifferentialGraded.RightModule R D) : Prop :=
  _root_.SerrePositivity.DifferentialGraded.moduleHomotopicallyProjective R D (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) M)
/-- 射影的右 dg 加群の全 dg 部分圏。 -/
abbrev ProjectiveDGModules := _root_.SerrePositivity.DifferentialGraded.DGFullSubcategory (_root_.SerrePositivity.DifferentialGraded.RightModule R D) (dgModuleProjectiveProperty R D)
/-- 射影的右 dg 加群の実 dg nerve。 -/
abbrev dgProjectiveModuleNerve := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (ProjectiveDGModules R D)
/-- 射影的加群は、零・標準 cone・標準 fiber で閉じる。 -/
lemma dgModuleProjectiveProperty_closed : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleClosedProperty R D
    (dgModuleProjectiveProperty R D) where
  zero := _root_.SerrePositivity.DifferentialGraded.moduleHomotopicallyProjective_of_isZero R D (_root_.SerrePositivity.DifferentialGraded.moduleZero_isZero R D)
  cone f hM hN := _root_.SerrePositivity.DifferentialGraded.moduleHomotopicallyProjective_cone R D hM hN f
  fiber f hM hN := _root_.SerrePositivity.DifferentialGraded.moduleHomotopicallyProjective_shift R D
    (_root_.SerrePositivity.DifferentialGraded.moduleHomotopicallyProjective_cone R D hM hN f) (-1)
/-- 全 Hom end による射影的加群の実 nerve は安定。 -/
theorem dgProjectiveModuleNerve_isStable : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable (dgProjectiveModuleNerve R D) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedModule_isStable R D _ (dgModuleProjectiveProperty_closed R D)
/-- 射影的加群の実包含は完全。 -/
theorem dgProjectiveModuleInclusion_isExactFunctor : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgFullSubcategoryInclusion R (RightModule R D)
      (dgModuleProjectiveProperty R D))) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedModuleInclusion_isExactFunctor R D _ (dgModuleProjectiveProperty_closed R D)
/-- 半自由加群から射影的加群への、全 Hom end を保つ実 dg 包含。 -/
def dgSemifreeToProjective : DGFunctor R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) (ProjectiveDGModules R D) where
  obj M := ⟨M.val, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeModule_isProjective R D M⟩
  map _ _ := 𝟙 _
  map_id _ := by simp only [Category.comp_id]; rfl
  map_comp _ _ _ := by
    simp only [Category.comp_id, tensorHom_id, id_whiskerRight, Category.id_comp]
    rfl
/-- 半自由模型と射影的模型の比較は全写像空間で充満忠実。 -/
lemma dgSemifreeToProjectiveNerve_isFullyFaithful :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgSemifreeToProjective R D)) := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerve_map_isFullyFaithful_of_homIso
  intro M N
  change IsIso (𝟙 (_root_.SerrePositivity.DifferentialGraded.moduleHom R D M.val N.val))
  infer_instance
end SerrePositivity.InfinityCategories.Project.DerivedCategories
