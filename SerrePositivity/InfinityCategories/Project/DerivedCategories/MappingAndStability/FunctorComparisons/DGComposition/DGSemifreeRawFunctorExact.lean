module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.Resolutions.DGSemifreeProjectiveEquivalence
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Actions.DGModuleFunctorExact
/-!
概要：半自由入力の周囲への実包含と、生の dg 関手への制限の完全性を示す。
方針：半自由・射影的模型の同値と射影的包含の完全性を合成する。
規約：生の出力の射影性は不要。使われ方：一般出力分解の Hom 試験の標的四角形。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
variable (R : Type u) [CommRing R] (D E : Type v)
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
omit [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E] in
/-- 同じ半自由入力の実包含と生の関手の完全性。 -/
lemma dgSemifreeToProjective_comp_inclusion :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeToProjective R D).comp
      (dgFullSubcategoryInclusion R (RightModule R D) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleProjectiveProperty R D)) =
      dgFullSubcategoryInclusion R (RightModule R D) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleSemifreeProperty R D) := by
  apply EnrichedFunctor.ext (_root_.SerrePositivity.DifferentialGraded.Complex R) (fun _ => rfl)
  intro X Y
  simp only [EnrichedFunctor.comp_map, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeToProjective, dgFullSubcategoryInclusion,
    Category.comp_id, eqToHom_refl]
omit [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E] in
/-- 同じ半自由入力の実包含と生の関手の完全性。 -/
lemma dgSemifreeModulesInclusion_isExactFunctor :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgFullSubcategoryInclusion R (RightModule R D)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleSemifreeProperty R D))) := by
  have h := congrArg (fun H => _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map H) (dgSemifreeToProjective_comp_inclusion R D)
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp] at h
  rw [← h]
  let := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isExactFunctor_of_isQCatEquivalence
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeToProjectiveNerve_isQCatEquivalence R D)
  let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveModuleInclusion_isExactFunctor R D
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.isExactFunctor_comp _ _
/-- 同じ半自由入力の実包含と生の関手の完全性。 -/
lemma dgSemifreeModuleFunctorRaw_isExactFunctor
    (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R (_root_.SerrePositivity.DifferentialGraded.RightModule R D) (_root_.SerrePositivity.DifferentialGraded.RightModule R E)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map
      ((_root_.SerrePositivity.DifferentialGraded.dgFullSubcategoryInclusion R (_root_.SerrePositivity.DifferentialGraded.RightModule R D)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleSemifreeProperty R D)).comp F)) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp]
  let := dgSemifreeModulesInclusion_isExactFunctor R D
  let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorNerve_isExactFunctor R D E F
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.isExactFunctor_comp _ _
end SerrePositivity.InfinityCategories.Project.DerivedCategories
