module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentHomologyBarCofork

/-!
概要：非退化 H(G) bar の一次微分の余核は実 bar のホモロジーである。
方針：実長完全列から得た余核列を、自然な零段階・層同型で移す。
規約：ホモロジー射は実包含から作る標準射である。
使われ方：coherent C1 のホモロジー比較同型。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
open CategoryTheory Limits DifferentialGraded SSet
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  {J : Type u} [PartialOrder J] [IsFiltered J]
  (G : (SSet.uliftFunctor.{max (u + 1) v, u}).obj (nerve J) ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D))

def dgCoherentBarHomologyBarSequence (x : D) (p : ℤ) : ShortComplex (ModuleCat.{u} R) :=
  ShortComplex.mk
    ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarNondegComplex R (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarHomologyDiagram R D G x (p + 1))).d 1 0)
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarHomologyBarAugmentation R D G x (p + 1))
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarHomologyBarAugmentation_d_one R D G x p)

def dgCoherentBarHomologyCokernelSequenceIso (x : D) (p : ℤ) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarHomologyCokernelSequence R D G x p ≅
      dgCoherentBarHomologyBarSequence R D G x p :=
  ShortComplex.isoMk
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarNaturalLayerHomologyIso R D G x 1 p (p + 1) (by omega))
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarZeroStageHomologyIso R D G x (p + 1))
    (Iso.refl _)
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarFirstConnecting_homologyBar R D G x p).symm
    (by
      change (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarZeroStageHomologyIso R D G x (p + 1)).hom ≫
        ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarZeroStageHomologyIso R D G x (p + 1)).inv ≫ _) = _ ≫ 𝟙 _
      rw [Iso.hom_inv_id_assoc, Category.comp_id]
      rfl)

def dgCoherentBarHomologyBarIsCokernel (x : D) (p : ℤ) :
    IsColimit (CokernelCofork.ofπ
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarHomologyBarAugmentation R D G x (p + 1))
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarHomologyBarAugmentation_d_one R D G x p)) := by
  have he := ShortComplex.exact_of_iso (dgCoherentBarHomologyCokernelSequenceIso R D G x p)
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarHomologyCokernelSequence_exact R D G x p)
  letI : Epi (HomologicalComplex.homologyMap
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarNormalizedStageInclusion R D G x 0) (p + 1)) :=
    (ModuleCat.epi_iff_surjective _).mpr
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarZeroStageHomology_surjective R D G x (p + 1))
  letI : Epi (dgCoherentBarHomologyBarSequence R D G x p).g := by
    change Epi ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarZeroStageHomologyIso R D G x (p + 1)).inv ≫ _)
    infer_instance
  exact he.gIsCokernel

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
