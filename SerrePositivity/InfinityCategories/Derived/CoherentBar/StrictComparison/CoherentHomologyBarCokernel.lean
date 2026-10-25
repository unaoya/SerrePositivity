module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentHomologyBarCofork

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
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {J : Type u} [PartialOrder J] [IsFiltered J]
  (G : (SSet.uliftFunctor.{max (u + 1) v, u}).obj (nerve J) ⟶
    dgNerve R (RightModule R D))

def dgCoherentBarHomologyBarSequence (x : D) (p : ℤ) : ShortComplex (ModuleCat.{u} R) :=
  ShortComplex.mk
    ((dgHomologyBarNondegComplex R (dgCoherentBarHomologyDiagram R D G x (p + 1))).d 1 0)
    (dgCoherentBarHomologyBarAugmentation R D G x (p + 1))
    (dgCoherentBarHomologyBarAugmentation_d_one R D G x p)

def dgCoherentBarHomologyCokernelSequenceIso (x : D) (p : ℤ) :
    dgCoherentBarHomologyCokernelSequence R D G x p ≅
      dgCoherentBarHomologyBarSequence R D G x p :=
  ShortComplex.isoMk
    (dgCoherentBarNaturalLayerHomologyIso R D G x 1 p (p + 1) (by omega))
    (dgCoherentBarZeroStageHomologyIso R D G x (p + 1))
    (Iso.refl _)
    (dgCoherentBarFirstConnecting_homologyBar R D G x p).symm
    (by
      change (dgCoherentBarZeroStageHomologyIso R D G x (p + 1)).hom ≫
        ((dgCoherentBarZeroStageHomologyIso R D G x (p + 1)).inv ≫ _) = _ ≫ 𝟙 _
      rw [Iso.hom_inv_id_assoc, Category.comp_id]
      rfl)

def dgCoherentBarHomologyBarIsCokernel (x : D) (p : ℤ) :
    IsColimit (CokernelCofork.ofπ
      (dgCoherentBarHomologyBarAugmentation R D G x (p + 1))
      (dgCoherentBarHomologyBarAugmentation_d_one R D G x p)) := by
  have he := ShortComplex.exact_of_iso (dgCoherentBarHomologyCokernelSequenceIso R D G x p)
    (dgCoherentBarHomologyCokernelSequence_exact R D G x p)
  letI : Epi (HomologicalComplex.homologyMap
      (dgCoherentBarNormalizedStageInclusion R D G x 0) (p + 1)) :=
    (ModuleCat.epi_iff_surjective _).mpr
      (dgCoherentBarZeroStageHomology_surjective R D G x (p + 1))
  letI : Epi (dgCoherentBarHomologyBarSequence R D G x p).g := by
    change Epi ((dgCoherentBarZeroStageHomologyIso R D G x (p + 1)).inv ≫ _)
    infer_instance
  exact he.gIsCokernel

end SerrePositivity.InfinityCategories
