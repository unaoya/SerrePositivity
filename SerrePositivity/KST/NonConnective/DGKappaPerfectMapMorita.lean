module
public import SerrePositivity.KST.NonConnective.DGKappaPerfectMapEquivalence
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGStableHomotopyNaturality
public import SerrePositivity.KST.SConstruction.PerfectDGMoritaHomotopy

/-!
概要：元の native dg 同値から、同じ主 Perf 延長の通常圏同値を得る。
方針：実 Perf 延長の native 同値を h/H⁰ 自然性と元の主導来比較へ通す。
規約：H⁰ 同値から dg 擬同値を推論しない。
使われ方：K-7 e の元の実 BF Morita 定理への入力。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.NonConnective

private theorem homotopyEquivalenceOfNative (R : Type u) [CommRing R]
    (C D : Type v) [DGCategory R C] [DGCategory R D] (f : DGFunctor R C D)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map f)) : f.onHomotopy.IsEquivalence := by
  let : (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map f)).toFunctor.IsEquivalence :=
    hf.choose.toHoEquivalence.isEquivalence_functor
  have : ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStableHomotopyEquivalence R C).functor ⋙ f.onHomotopy).IsEquivalence :=
    Functor.isEquivalence_of_iso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStableHomotopyEquivalence_naturalityIso R C D f)
  exact Functor.isEquivalence_of_comp_left (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStableHomotopyEquivalence R C).functor
    f.onHomotopy

variable (R : Type u) [CommRing R] (C D : Type (max (u + 1) v))
  [DGCategory R C] [Small.{u} C] [DGCategory R D] [Small.{u} D]
  [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R C] [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R D]

/-- 同じ元の射の native 同値性は、元の主 Perf 延長の同値性を与える。 -/
theorem dgKappaPerfectExtension_isEquivalence_of_native (f : DGFunctor R C D)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map f)) :
    (quasiEquivalencePerfectExtension R C D f).IsEquivalence := by
  let : (perfectDGExtension R C D f).onHomotopy.IsEquivalence :=
    homotopyEquivalenceOfNative R _ _ (perfectDGExtension R C D f)
      (dgKappaPerfectMap_isQCatEquivalence R C D f hf)
  have : (perfectDGModuleToPerfect R C Set.univ ⋙
      quasiEquivalencePerfectExtension R C D f).IsEquivalence :=
    Functor.isEquivalence_of_iso (perfectDGExtensionPerfectComparison R C D f).symm
  exact Functor.isEquivalence_of_comp_left (perfectDGModuleToPerfect R C Set.univ)
    (quasiEquivalencePerfectExtension R C D f)

end SerrePositivity.KST.NonConnective
