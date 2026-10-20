module
public import SerrePositivity.KST.SConstruction.PerfectDGMoritaHomotopy
public import SerrePositivity.KST.SConstruction.DGModuleHomShiftCriterion
public import SerrePositivity.KST.SConstruction.PerfectDGExtensionExact
public import SerrePositivity.KST.SConstruction.DGQuasiEquivalence

/-! # 主 Perf 作用の同値から実 dg nerve の Morita 同値へ
概要：主 Perf 作用が同値なら、元の実 Perf dg 延長は全 Hom 複体で擬同型となる。
方針：実 H⁰ 比較と全 source shift の零次数判定から、dg 準同値を構成する。
規約：一般入力の準同値を Morita 同値の定義にはしない。使われ方：K-4d の不変性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories SerrePositivity.SimplicialModel
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)
  [(quasiEquivalencePerfectExtension A D E F).IsEquivalence]

/-- 主 Perf 作用の同値は、実 Perf dg 延長の全 Hom 複体の擬同型を与える。 -/
lemma perfectDGExtension_homQuasiIso : HomQuasiIso (perfectDGExtension A D E F) := by
  let := perfectDGExtensionHomotopy_isEquivalence A D E F
  intro M N
  change QuasiIso ((dgModuleExtension A D E F).map M.val N.val)
  apply dgModuleHom_quasiIso_of_shift_zero A D E _ M.val N.val
  intro s
  let Ms := perfectDGModuleShiftObj A D Set.univ s M
  exact dgHom_quasiIsoAt_zero_of_bijective (perfectDGExtension A D E F)
    (ForgetEnrichment.of (Complex A) Ms) (ForgetEnrichment.of (Complex A) N)
    ((Functor.FullyFaithful.ofFullyFaithful
      (perfectDGExtension A D E F).onHomotopy).map_bijective _ _)

/-- 主 Perf 作用の同値は、実 Perf dg 延長の準同値を与える。 -/
lemma perfectDGExtension_quasiEquivalence : QuasiEquivalence (perfectDGExtension A D E F) := by
  let := perfectDGExtensionHomotopy_isEquivalence A D E F
  exact ⟨perfectDGExtension_homQuasiIso A D E F, inferInstance⟩

end SerrePositivity.KST.SConstruction
