module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomSpaces.HomotopyRepresentations.MilnorAlgebraDiagonalHom
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.ComparisonModels.Size
public import SerrePositivity.KST.SConstruction.PerfectDGFullyFaithful
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.LocalizationAndRoofs.DGFunctorQuasiIsoFullyFaithful
/-!
概要：Milnor 自由対角の同じ一回 Perf 延長は全 Hom で準同型、nerve で充満忠実。
方針：照合済みの元の Hom 作用へ、既存の実 Perf 延長と一般 Hom 準同型判定を適用する。
規約：K-S• の小 Perf 対角との比較は後続工程。終域を同一視しない。
使われ方：元の Perf 対角の充満忠実性へ移すための実関手を供給する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded SSet
open KST.SConstruction
variable (R : Type u) [CommRing R] (d : DGOdotInput R)
def dgGluingMilnorPerfectExtension :
    DGFunctor R (PerfectDGModule R (_root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R d.source))
      (PerfectDGModule R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingMilnorGeneratorCategory R d)) :=
  perfectDGExtension R (_root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R d.source) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingMilnorGeneratorCategory R d)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorAlgebraDiagonal R d)
lemma dgGluingMilnorPerfectExtension_homQuasiIso (h : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingMilnorSquare R d) :
    _root_.SerrePositivity.DifferentialGraded.HomQuasiIso (dgGluingMilnorPerfectExtension R d) :=
  perfectDGExtension_homQuasiIso_of_homQuasiIso R (_root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R d.source)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingMilnorGeneratorCategory R d) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorAlgebraDiagonal R d)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorAlgebraDiagonal_homQuasiIso R d h)
lemma dgGluingMilnorPerfectExtension_isFullyFaithful (h : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingMilnorSquare R d) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgGluingMilnorPerfectExtension R d)) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerve_map_isFullyFaithful_of_quasiIso (dgGluingMilnorPerfectExtension R d)
    (dgGluingMilnorPerfectExtension_homQuasiIso R d h)
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
