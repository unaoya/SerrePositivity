module
public import SerrePositivity.InfinityCategories.Derived.DGPerfectModulesInfinity
public import SerrePositivity.InfinityCategories.Derived.DGPretriangulatedYonedaExact
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]

def dgPerfectYoneda : DGFunctor R D (PerfectDGModule R D) where
  obj x := ⟨representable R x, representable_homotopicallyProjective R D x,
    modulePerfectOver_representable R D x (Set.mem_univ _)⟩
  map x y := (dgYoneda R D).map x y
  map_id x := (dgYoneda R D).map_id x
  map_comp x y z := (dgYoneda R D).map_comp x y z

lemma dgPerfectYoneda_inclusion :
    (dgPerfectYoneda R D).comp (perfectDGModuleInclusion R D Set.univ) = dgYoneda R D := by
  apply EnrichedFunctor.ext (Complex R) (fun _ => rfl)
  intro x y
  simp only [EnrichedFunctor.comp_map, perfectDGModuleInclusion,
    dgFullSubcategoryInclusion, Category.comp_id, eqToHom_refl, Category.id_comp]

def dgPerfectYonedaCommonFunctor :
    DGFunctor R (DGUniverseLift.{v, max (u+1) v} D) (PerfectDGModule R D) :=
  (dgUniverseLiftDown R D).comp (dgPerfectYoneda R D)

abbrev dgPerfectYonedaInfinity := dgNerve.map (dgPerfectYonedaCommonFunctor R D)

lemma dgPerfectYonedaInfinity_isFullyFaithful : IsFullyFaithful (dgPerfectYonedaInfinity R D) := by
  apply dgNerve_map_isFullyFaithful_of_homIso
  intro x y
  change IsIso (𝟙 _ ≫ (dgYonedaIso (D := D) R x.label.down
    (representable R y.label.down)).inv)
  infer_instance

lemma dgPerfectYonedaInfinity_inclusion :
    dgPerfectYonedaInfinity R D ≫ dgNerve.map (perfectDGModuleInclusion R D Set.univ) =
      dgNerve.map ((dgUniverseLiftDown.{u, v, max (u+1) v} R D).comp (dgYoneda R D)) := by
  rw [← dgNerve.map_comp]
  congr 1

lemma dgPerfectYonedaInfinity_isExactFunctor [IsDGPretriangulated R D] :
    IsExactFunctor (dgPerfectYonedaInfinity R D) where
  preservesZero := dgFunctorNerve_preservesZeroVertices _
  preservesCofiber t ht := by
    let := dgPretriangulatedYoneda_isExactFunctor R D
    apply isColimitCone_of_fullInclusion R (RightModule R D)
      (modulePerfectProjectiveOver R D Set.univ) (pushoutCocone _)
    change IsPushoutSquare ((t.square ≫ dgPerfectYonedaInfinity R D) ≫
      dgNerve.map (perfectDGModuleInclusion R D Set.univ))
    rw [Category.assoc, dgPerfectYonedaInfinity_inclusion]
    exact IsExactFunctor.preservesCofiber
      (F := dgNerve.map ((dgUniverseLiftDown R D).comp (dgYoneda R D))) t ht

end SerrePositivity.InfinityCategories
