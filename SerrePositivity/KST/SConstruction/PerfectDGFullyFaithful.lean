module
public import SerrePositivity.KST.SConstruction.PerfectDGMoritaHomotopy
public import SerrePositivity.KST.SConstruction.DGModuleHomShiftCriterion
public import SerrePositivity.KST.SConstruction.PerfectDGExtensionExact
public import SerrePositivity.DifferentialGraded.Derived.FunctorExtensionAdjunction

/-! # Hom 準同型な元の dg 関手の実 Perf 延長の充満忠実性
概要：本質的全射性なしで、元の実 Perf 延長の全 Hom 準同型性を証明する。
方針：主導来延長の充満忠実性を Perf と実 H⁰ 比較へ移し、全 source shift で判定する。
規約：Morita 同値を仮定しない。使われ方：元の右軸包含の実 Perf 延長。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory
open SerrePositivity.DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (F : DGFunctor R C D) (hF : HomQuasiIso F)

/-- 元の主導来延長の Perf 制限は、本質的全射性なしで充満忠実。 -/
def perfectDGMainExtensionFullyFaithful :
    (quasiEquivalencePerfectExtension R C D F).FullyFaithful := by
  have hc : (quasiEquivalencePerfectExtension R C D F ⋙
      perfectModuleInclusion R D Set.univ).FullyFaithful := by
    change (perfectModuleInclusion R C Set.univ ⋙ dgDerivedExtension R C D F).FullyFaithful
    exact (modulePerfectOver R C Set.univ).fullyFaithfulι.comp
      (dgDerivedExtensionFullyFaithful R C D F hF)
  have : (perfectModuleInclusion R D Set.univ).Faithful :=
    (modulePerfectOver R D Set.univ).fullyFaithfulι.faithful
  exact Functor.FullyFaithful.ofCompFaithful hc

/-- 元の実 Perf 延長の H⁰ は、同じ実比較を通って充満忠実。 -/
def perfectDGExtensionHomotopyFullyFaithful :
    (perfectDGExtension R C D F).onHomotopy.FullyFaithful := by
  have hc : (perfectDGModuleToPerfect R C Set.univ ⋙
      quasiEquivalencePerfectExtension R C D F).FullyFaithful :=
    (Functor.FullyFaithful.ofFullyFaithful _).comp
      (perfectDGMainExtensionFullyFaithful R C D F hF)
  exact Functor.FullyFaithful.ofCompFaithful
    (hc.ofIso (perfectDGExtensionPerfectComparison R C D F))

include hF in
/-- 元の Hom 準同型な dg 関手の実 Perf 延長は、全 Hom 複体で準同型を誘導する。 -/
lemma perfectDGExtension_homQuasiIso_of_homQuasiIso :
    HomQuasiIso (perfectDGExtension R C D F) := by
  intro M N
  change QuasiIso ((dgModuleExtension R C D F).map M.val N.val)
  apply dgModuleHom_quasiIso_of_shift_zero R C D _ M.val N.val
  intro s
  let Ms := perfectDGModuleShiftObj R C Set.univ s M
  exact dgHom_quasiIsoAt_zero_of_bijective (perfectDGExtension R C D F)
    (ForgetEnrichment.of (Complex R) Ms) (ForgetEnrichment.of (Complex R) N)
    ((perfectDGExtensionHomotopyFullyFaithful R C D F hF).map_bijective _ _)

end SerrePositivity.KST.SConstruction
