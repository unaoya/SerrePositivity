module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentLayerRemainder
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
概要：実正規化 coherent bar の隣接段階と次元層は短完全列をなす。
方針：次数ごとの単射・全射と、最高次元を除く残余の一段下降を合わせる。
規約：全高次 HA 成分を含む実微分を保持する。
使われ方：単体次元フィルトレーションの段階商と内部複体の同定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (G : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgNerve R (RightModule R D))

lemma dgCoherentBarStageMap_toLayer_zero (x : D) (n : ℕ) :
    dgCoherentBarNormalizedStageMap R D G x (Nat.le_succ n) ≫
      dgCoherentBarStageToLayer R D G x (n + 1) = 0 := by
  ext q z
  exact dgCoherentBarLayerProjection_annihilate R D G x q (Nat.lt_succ_self n) z.val z.property

def dgCoherentBarLayerSequence (x : D) (n : ℕ) : ShortComplex (Complex R) :=
  ShortComplex.mk (dgCoherentBarNormalizedStageMap R D G x (Nat.le_succ n))
    (dgCoherentBarStageToLayer R D G x (n + 1)) (dgCoherentBarStageMap_toLayer_zero R D G x n)

lemma dgCoherentBarLayerSequence_shortExact (x : D) (n : ℕ) :
    (dgCoherentBarLayerSequence R D G x n).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro q
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · rw [ShortComplex.moduleCat_exact_iff]
    intro z hz
    change (moduleDegreeEvaluation R D x q).map (dgCoherentBarLayerProjection R D G (n + 1))
      z.val = 0 at hz
    have hm := dgCoherentBarLayerProjection_kernel_mem R D G x q n z.val z.property hz
    exact ⟨⟨z.val, hm⟩, rfl⟩
  · apply (ModuleCat.mono_iff_injective _).mpr
    change Function.Injective (Submodule.inclusion
      (dgCoherentBarNormalizedDegreeFiltration_mono R D G x q (Nat.le_succ n)))
    exact Submodule.inclusion_injective _
  · exact (ModuleCat.epi_iff_surjective _).mpr (dgCoherentBarStageToLayer_surjective R D G x q (n + 1))

end SerrePositivity.InfinityCategories
