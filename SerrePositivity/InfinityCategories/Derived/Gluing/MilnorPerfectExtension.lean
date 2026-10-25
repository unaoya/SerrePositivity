module
public import SerrePositivity.InfinityCategories.Derived.Gluing.MilnorAlgebraDiagonalHom
public import SerrePositivity.InfinityCategories.Derived.Gluing.Size
public import SerrePositivity.KST.SConstruction.PerfectDGFullyFaithful
public import SerrePositivity.InfinityCategories.Derived.DGFunctorQuasiIsoFullyFaithful
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open KST.SConstruction
variable (R : Type u) [CommRing R] (d : DGOdotInput R)
def dgGluingMilnorPerfectExtension :
    DGFunctor R (PerfectDGModule R (dgAlgebraCategory R d.source))
      (PerfectDGModule R (DGGluingMilnorGeneratorCategory R d)) :=
  perfectDGExtension R (dgAlgebraCategory R d.source) (DGGluingMilnorGeneratorCategory R d)
    (dgGluingMilnorAlgebraDiagonal R d)
lemma dgGluingMilnorPerfectExtension_homQuasiIso (h : DGGluingMilnorSquare R d) :
    HomQuasiIso (dgGluingMilnorPerfectExtension R d) :=
  perfectDGExtension_homQuasiIso_of_homQuasiIso R (dgAlgebraCategory R d.source)
    (DGGluingMilnorGeneratorCategory R d) (dgGluingMilnorAlgebraDiagonal R d)
    (dgGluingMilnorAlgebraDiagonal_homQuasiIso R d h)
lemma dgGluingMilnorPerfectExtension_isFullyFaithful (h : DGGluingMilnorSquare R d) :
    IsFullyFaithful (dgNerve.map (dgGluingMilnorPerfectExtension R d)) :=
  dgNerve_map_isFullyFaithful_of_quasiIso (dgGluingMilnorPerfectExtension R d)
    (dgGluingMilnorPerfectExtension_homQuasiIso R d h)
end SerrePositivity.InfinityCategories
