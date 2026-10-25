module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentZeroStageKernel
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentZeroStageHomologySurjective

/-!
概要：実正規化 bar のホモロジーは、最初の連結射の余核である。
方針：有限 support による全射性と核の下降を、加群の完全列へまとめる。
規約：実 bar と実長完全列を用い、形式的スペクトル系列の収束を仮定しない。
使われ方：非退化 H(G) bar の零次ホモロジーとの同定。
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

lemma dgCoherentBarFirstConnecting_inclusion_zero (x : D) (p : ℤ) :
    (dgCoherentBarLayerSequence_shortExact R D G x 0).δ p (p + 1) (by simp) ≫
      HomologicalComplex.homologyMap
        (dgCoherentBarNormalizedStageInclusion R D G x 0) (p + 1) = 0 := by
  rw [← dgCoherentBarNormalizedStageMap_inclusion R D G x (Nat.le_succ 0),
    HomologicalComplex.homologyMap_comp, ← Category.assoc]
  erw [(dgCoherentBarLayerSequence_shortExact R D G x 0).δ_comp p (p + 1) (by simp)]
  exact zero_comp

def dgCoherentBarHomologyCokernelSequence (x : D) (p : ℤ) : ShortComplex (ModuleCat.{u} R) :=
  ShortComplex.mk
    ((dgCoherentBarLayerSequence_shortExact R D G x 0).δ p (p + 1) (by simp))
    (HomologicalComplex.homologyMap
      (dgCoherentBarNormalizedStageInclusion R D G x 0) (p + 1))
    (dgCoherentBarFirstConnecting_inclusion_zero R D G x p)

lemma dgCoherentBarHomologyCokernelSequence_exact (x : D) (p : ℤ) :
    (dgCoherentBarHomologyCokernelSequence R D G x p).Exact := by
  rw [ShortComplex.moduleCat_exact_iff]
  intro a ha
  exact dgCoherentBarZeroStageHomology_kernel R D G x p a ha

def dgCoherentBarHomologyIsCokernel (x : D) (p : ℤ) :
    IsColimit (CokernelCofork.ofπ
      (HomologicalComplex.homologyMap
        (dgCoherentBarNormalizedStageInclusion R D G x 0) (p + 1))
      (dgCoherentBarFirstConnecting_inclusion_zero R D G x p)) := by
  letI : Epi (HomologicalComplex.homologyMap
      (dgCoherentBarNormalizedStageInclusion R D G x 0) (p + 1)) :=
    (ModuleCat.epi_iff_surjective _).mpr
      (dgCoherentBarZeroStageHomology_surjective R D G x (p + 1))
  letI : Epi (dgCoherentBarHomologyCokernelSequence R D G x p).g := by
    change Epi (HomologicalComplex.homologyMap
      (dgCoherentBarNormalizedStageInclusion R D G x 0) (p + 1))
    infer_instance
  exact (dgCoherentBarHomologyCokernelSequence_exact R D G x p).gIsCokernel

end SerrePositivity.InfinityCategories
