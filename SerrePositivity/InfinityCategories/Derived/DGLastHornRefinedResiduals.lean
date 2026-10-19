module
public import SerrePositivity.InfinityCategories.Derived.DGLastHornRefinedComponents
public import SerrePositivity.InfinityCategories.Derived.DGLastHornCochains
public import SerrePositivity.InfinityCategories.Derived.DGTriangleResidualPrecompose
public import SerrePositivity.InfinityCategories.DGNerve.HomHEqAlgebra

/-! # 実閉細分ホーンの二残差と元の R・K の前合成

概要：貼った新ホーンから回収する二残差が、元の二残差の同じ閉前合成と型付きで一致する。
方針：回収辺・三角 cochain の異種等号を合成・差へ移し、残差の前合成公式を使う。
規約：新旧対象族の等式を保持。使われ方：実 Q・A を新ホーンの二未知解にする。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]
variable (σ : (Λ[3, 3] : SSet.{max u v}) ⟶ dgNerve A D) (q : D)
variable (s : ForgetEnrichment.of (Complex A) q ⟶
  ForgetEnrichment.of (Complex A) ((HornData.knownData σ).obj 0))

/-- 貼った新ホーンの R は、元の R の同じ実閉射による前合成。 -/
lemma dgLastHornSourceRefinement_missingResidual :
    HEq (dgLastHornMissingResidual (dgLastHornSourceRefinement σ q s))
      (dgGradedPrecompose A D 0 (dgLastHornMissingResidual σ) s) := by
  have hc := gradedHom_compose_heq (k := 0) (k' := 0)
    (dgLastHornSourceRefinement_obj0 σ q s) (dgLastHornSourceRefinement_obj1 σ q s)
    (dgLastHornSourceRefinement_obj2 σ q s) rfl rfl rfl _ _ _ _
    (dgLastHornSourceRefinement_edge12 σ q s) (dgLastHornSourceRefinement_edge01 σ q s)
    (by decide) (by decide)
  have hr := gradedHom_sub_heq (dgLastHornSourceRefinement_obj0 σ q s)
    (dgLastHornSourceRefinement_obj2 σ q s) rfl _ _ _ _ hc
    (dgLastHornSourceRefinement_edge02 σ q s)
  exact hr.trans (heq_of_eq (dgTriangleMissingResidual_precompose
    (closedHomEquiv A D _ _ s).val ((HornData.knownData σ).edgeHom 0 1 (by decide))
    ((HornData.knownData σ).edgeHom 0 2 (by decide))
    ((HornData.knownData σ).edgeHom 1 2 (by decide))))

/-- 貼った新ホーンの K も、元の K の同じ実閉射による前合成。 -/
lemma dgLastHornSourceRefinement_topResidual :
    HEq (dgLastHornTopResidual (dgLastHornSourceRefinement σ q s))
      (dgGradedPrecompose A D (-1) (dgLastHornTopResidual σ) s) := by
  have hc := gradedHom_compose_heq (k := -1) (k' := -1)
    (dgLastHornSourceRefinement_obj0 σ q s) (dgLastHornSourceRefinement_obj1 σ q s)
    (dgLastHornSourceRefinement_obj3 σ q s) rfl rfl rfl _ _ _ _
    (dgLastHornSourceRefinement_triangle123 σ q s) (dgLastHornSourceRefinement_edge01 σ q s)
    (by decide) (by decide)
  have h₁ := gradedHom_sub_heq (dgLastHornSourceRefinement_obj0 σ q s)
    (dgLastHornSourceRefinement_obj3 σ q s) rfl _ _ _ _
    (dgLastHornSourceRefinement_triangle023 σ q s) hc
  have hr := gradedHom_sub_heq (dgLastHornSourceRefinement_obj0 σ q s)
    (dgLastHornSourceRefinement_obj3 σ q s) rfl _ _ _ _ h₁
    (dgLastHornSourceRefinement_triangle013 σ q s)
  exact hr.trans (heq_of_eq (dgTriangleTopResidual_precompose (closedHomEquiv A D _ _ s).val
    ((HornData.knownData σ).edgeHom 0 1 (by decide))
    ((HornData.knownData σ).tripleHom 0 1 3 (by decide) (by decide))
    ((HornData.knownData σ).tripleHom 0 2 3 (by decide) (by decide))
    ((HornData.knownData σ).tripleHom 1 2 3 (by decide) (by decide))))

end SerrePositivity.InfinityCategories
