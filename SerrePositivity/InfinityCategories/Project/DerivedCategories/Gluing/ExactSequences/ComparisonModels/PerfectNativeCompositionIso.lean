module
public import SerrePositivity.KST.SConstruction.PerfectDGExtensionComposition
public import SerrePositivity.KST.SConstruction.DGStandardClosedComparisonIso
public import SerrePositivity.KST.SConstruction.DGStandardFunctorIsoReflection
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.DGComposition.DGUniverseLiftFunctor
/-!
概要：異なる対象宇宙の実 Perf 延長の合成と下降を全関手同型で比較する。
方針：元の全次数自然な実合成同型を native nerve に反映する。
規約：係数宇宙と入力関手を固定する。使われ方：元二脚の固定宇宙への照合。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory SSet DifferentialGraded KST.SConstruction
variable (R : Type u) [CommRing R]

-- Perf の対象宇宙が一致する範囲で、元入力の対象宇宙は独立にする。
def perfectNativeCompositionDownIso
    (D E : Type (max (u + 1) v)) (T : Type v)
    [DGCategory R D] [Small.{u} D] [DGCategory R E] [Small.{u} E]
    [DGCategory R T] [Small.{u} T]
    (F : DGFunctor R D E) (G : DGFunctor R E T) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (perfectDGExtension R D E F) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (perfectDGExtension R E T G))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (perfectDGExtension R D T (F.comp G))) := by
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp]
  exact dgStandardFunctorIso_to_native (dgStandardClosedComparisonIso _ _
    (perfectDGExtensionCompositionAt R D E T F G)
    (perfectDGExtensionCompositionAt_naturality R D E T F G))

def perfectNativeDownCompositionIso
    (D : Type (max (u + 1) v)) (E T : Type v)
    [DGCategory R D] [Small.{u} D] [DGCategory R E] [Small.{u} E]
    [DGCategory R T] [Small.{u} T]
    (F : DGFunctor R D E) (G : DGFunctor R E T) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (perfectDGExtension R D E F) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (perfectDGExtension R E T G))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (perfectDGExtension R D T (F.comp G))) := by
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp]
  exact dgStandardFunctorIso_to_native (dgStandardClosedComparisonIso _ _
    (perfectDGExtensionCompositionAt R D E T F G)
    (perfectDGExtensionCompositionAt_naturality R D E T F G))

variable (D E : Type v) [DGCategory R D] [Small.{u} D]
    [DGCategory R E] [Small.{u} E]
    [Small.{u} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{v, u + 1} D)]
    [Small.{u} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{v, u + 1} E)]

def perfectNativeDownMapComparison (F : DGFunctor R D E) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (perfectDGExtension R _ _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftFunctor.{u, v, v, u + 1, u + 1} F)) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (perfectDGExtension R _ _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown.{u, v, u + 1} R E)))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (perfectDGExtension R _ _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown.{u, v, u + 1} R D)) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (perfectDGExtension R D E F)) := by
  let a := perfectNativeCompositionDownIso R _ _ _
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftFunctor.{u, v, v, u + 1, u + 1} F)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown.{u, v, u + 1} R E)
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftFunctor_comp_down] at a
  exact a.trans (perfectNativeDownCompositionIso R _ _ _
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown.{u, v, u + 1} R D) F).symm

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
