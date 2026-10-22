module

public import SerrePositivity.KST.LocalizingInvariants.DGExtensionCompositionNerveIso
public import SerrePositivity.InfinityCategories.Derived.DGPerfectExtensionInfinity
public import SerrePositivity.InfinityCategories.F1.FullyFaithfulPostcomposition

/-!
概要：D の元の実 Perf 延長の合成を、関手 ∞ 圏の実同型で比較する。
方針：元の全加群上の比較を前合成し、充満 dg 部分圏の包含で反映する。
規約：Perf と延長を再構成しない。使われ方：元の局所化不変量の値の塔。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.InfinityCategories.DGNerve
namespace SerrePositivity.KST.LocalizingInvariants
variable (R : Type u) [CommRing R] (D E T : Type v)
  [DGCategory R D] [Small.{u} D] [DGCategory R E] [Small.{u} E]
  [DGCategory R T] [Small.{u} T]

/-- 元の実 perfect 加群から全 dg 加群への充満包含。 -/
def dgPerfectUnderlying : DGFunctor R (PerfectDGModule R D) (RightModule R D) :=
  dgFullSubcategoryInclusion R (RightModule R D) (modulePerfectProjectiveOver R D Set.univ)

lemma dgPerfectExtensionInfinity_underlying (F : DGFunctor R D E) :
    dgPerfectExtensionInfinity R D E F ≫ dgNerve.map (dgPerfectUnderlying R E) =
      dgNerve.map (dgPerfectUnderlying R D) ≫ dgNerve.map (dgModuleExtension R D E F) := by
  change dgNerve.map (dgPerfectModuleExtension R D E F) ≫
      dgNerve.map (dgPerfectUnderlying R E) =
    dgNerve.map (dgPerfectUnderlying R D) ≫ dgNerve.map (dgModuleExtension R D E F)
  rw [← dgNerve.map_comp, ← dgNerve.map_comp]
  exact congrArg dgNerve.map (dgFullFunctorRestriction_inclusion R _ _
    (dgModuleExtension R D E F) _ _ (dgModuleExtension_perfectProjective R D E F))

/-- 元の二つの実 Perf 延長の合成は、元の合成関手に沿う実 Perf 延長と同型。 -/
def dgPerfectExtensionCompositionIso (F : DGFunctor R D E) (G : DGFunctor R E T) :
    FunctorIso (dgPerfectExtensionInfinity R D E F ≫ dgPerfectExtensionInfinity R E T G)
      (dgPerfectExtensionInfinity R D T (F.comp G)) := by
  have hi := dgFullSubcategoryInclusionNerve_isFullyFaithful R (RightModule R T)
    (modulePerfectProjectiveOver R T Set.univ)
  apply hi.preimageFunctorIso
  change FunctorIso
    ((dgPerfectExtensionInfinity R D E F ≫ dgPerfectExtensionInfinity R E T G) ≫
      dgNerve.map (dgPerfectUnderlying R T))
    (dgPerfectExtensionInfinity R D T (F.comp G) ≫ dgNerve.map (dgPerfectUnderlying R T))
  rw [Category.assoc, dgPerfectExtensionInfinity_underlying R E T G,
    ← Category.assoc, dgPerfectExtensionInfinity_underlying R D E F,
    dgPerfectExtensionInfinity_underlying R D T (F.comp G)]
  simpa only [Category.assoc] using
    (dgExtensionCompositionInfinityIso R D E T F G).precomp
      (dgNerve.map (dgPerfectUnderlying R D))

end SerrePositivity.KST.LocalizingInvariants
