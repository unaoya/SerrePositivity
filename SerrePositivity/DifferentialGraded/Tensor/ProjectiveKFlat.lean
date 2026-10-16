module
public import SerrePositivity.DifferentialGraded.Tensor.ProjectiveComparison
public import SerrePositivity.DifferentialGraded.Tensor.Semifree

/-! # 主Homによる射影性から相対K-flat性への橋渡し -/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 全Hom endによるhomotopical projectivityは相対K-flat性を含意する。 -/
lemma moduleHomotopicallyProjective_relativeKFlat {M : ModuleCategory A D}
    (hM : moduleHomotopicallyProjective A D M) :
    moduleRelativeKFlat A D (ForgetEnrichment.to (Complex A) M) := by
  obtain ⟨P, q, hP, hk, _, hq⟩ := exists_relativeKFlat_resolution A D M
  intro L hL
  exact cochainAcyclic_of_homotopyEquiv (hk L hL)
    (BalancedTensor.rightTensorProjectiveHomotopyEquiv A D L
      (moduleSemifree_homotopicallyProjective A D hP) hM q hq)

end SerrePositivity.DifferentialGraded
