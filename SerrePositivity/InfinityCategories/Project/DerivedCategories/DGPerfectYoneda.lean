module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGPerfectModulesInfinity
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGPretriangulatedYonedaExact
public import SerrePositivity.DifferentialGraded.Functor.QuasiEquivalence
/-!
概要：元の dg Yoneda を実 perfect 加群へ因子化し、共通宇宙の完全充満忠実射を作る。
方針：代表加群の射影性と perfect 性を対象に保持し、元の全 Hom 写像を使う。
規約：全 Perf の Small 性を要求せず、既存の Yoneda を変更しない。
使われ方：D-21 の前三角 dg 圏の native 冪等完備化。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]

def dgPerfectYoneda : _root_.SerrePositivity.DifferentialGraded.DGFunctor R D (_root_.SerrePositivity.DifferentialGraded.PerfectDGModule R D) where
  obj x := ⟨_root_.SerrePositivity.DifferentialGraded.representable R x, _root_.SerrePositivity.DifferentialGraded.representable_homotopicallyProjective R D x,
    _root_.SerrePositivity.DifferentialGraded.modulePerfectOver_representable R D x (Set.mem_univ _)⟩
  map x y := (_root_.SerrePositivity.DifferentialGraded.dgYoneda R D).map x y
  map_id x := (_root_.SerrePositivity.DifferentialGraded.dgYoneda R D).map_id x
  map_comp x y z := (_root_.SerrePositivity.DifferentialGraded.dgYoneda R D).map_comp x y z

lemma dgPerfectYoneda_inclusion :
    (dgPerfectYoneda R D).comp (_root_.SerrePositivity.DifferentialGraded.perfectDGModuleInclusion R D Set.univ) = dgYoneda R D := by
  apply EnrichedFunctor.ext (_root_.SerrePositivity.DifferentialGraded.Complex R) (fun _ => rfl)
  intro x y
  simp only [EnrichedFunctor.comp_map, _root_.SerrePositivity.DifferentialGraded.perfectDGModuleInclusion,
    _root_.SerrePositivity.DifferentialGraded.dgFullSubcategoryInclusion, Category.comp_id, eqToHom_refl, Category.id_comp]

def dgPerfectYonedaCommonFunctor :
    DGFunctor R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{v, max (u+1) v} D) (PerfectDGModule R D) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown R D).comp (dgPerfectYoneda R D)

abbrev dgPerfectYonedaInfinity := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgPerfectYonedaCommonFunctor R D)

lemma dgPerfectYonedaInfinity_isFullyFaithful : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (dgPerfectYonedaInfinity R D) := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerve_map_isFullyFaithful_of_homIso
  intro x y
  change IsIso (𝟙 _ ≫ (_root_.SerrePositivity.DifferentialGraded.dgYonedaIso (D := D) R x.label.down
    (_root_.SerrePositivity.DifferentialGraded.representable R y.label.down)).inv)
  infer_instance

lemma dgPerfectYonedaInfinity_inclusion :
    dgPerfectYonedaInfinity R D ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (perfectDGModuleInclusion R D Set.univ) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown.{u, v, max (u+1) v} R D).comp (dgYoneda R D)) := by
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp]
  congr 1

lemma dgPerfectYonedaInfinity_isExactFunctor [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R D] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (dgPerfectYonedaInfinity R D) where
  preservesZero := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorNerve_preservesZeroVertices _
  preservesCofiber t ht := by
    let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPretriangulatedYoneda_isExactFunctor R D
    apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.isColimitCone_of_fullInclusion R (RightModule R D)
      (modulePerfectProjectiveOver R D Set.univ) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutCocone _)
    change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare ((t.square ≫ dgPerfectYonedaInfinity R D) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (perfectDGModuleInclusion R D Set.univ))
    rw [Category.assoc, dgPerfectYonedaInfinity_inclusion]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesCofiber
      (F := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown R D).comp (dgYoneda R D))) t ht

end SerrePositivity.InfinityCategories.Project.DerivedCategories
