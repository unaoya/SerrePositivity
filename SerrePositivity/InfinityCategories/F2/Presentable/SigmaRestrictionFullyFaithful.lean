module

public import SerrePositivity.InfinityCategories.F2.Presentable.SigmaSiftedContinuousLeftKan
public import SerrePositivity.InfinityCategories.F2.Presentable.SiftedFunctorRestriction
public import SerrePositivity.InfinityCategories.F1B.KanExtension.LeftCanonicalMapping

/-!
概要：sifted 保存関手からの元の P_Σ Yoneda 制限射自身が、全写像空間で充満忠実。
方針：元の保存関手の標準 Kan 条件を、元の制限の pinched Hom 比較へ適用する。
規約：本質的全射性・延長の保存性は仮定せず、充満忠実性の証拠も元の射へ構成。
使われ方：P_Σ の全関手 ∞ 圏の普遍性の充満忠実性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 元の sifted 保存関手からの、元の Yoneda 制限射自身は全写像空間で充満忠実。 -/
lemma sigmaSiftedContinuousRestriction_isFullyFaithful (C : SSet.{u}) [Quasicategory C]
    (hC : ∀ (J : Type u) [Finite J] (d : nerve (Discrete J) ⟶ C.op), HasLimit d)
    (D : SSet.{u + 1}) [Quasicategory D] :
    IsFullyFaithful (sigmaSiftedContinuousRestriction C D) := by
  intro x y
  let F := (functorVertexEquiv (SigmaPresheafInfinity C) D).symm x.val
  let G := (functorVertexEquiv (SigmaPresheafInfinity C) D).symm y.val
  have hF : PreservesSmallSiftedColimits F := fullSubcomplexOnVertices_vertex x
  have hf : functorVertex F = x.val := (functorVertexEquiv _ _).apply_symm_apply _
  have hg : functorVertex G = y.val := (functorVertexEquiv _ _).apply_symm_apply _
  have hm := F1B.kanLeftCanonical_pinchedHomMap_equivalence (sigmaYonedaInfinityMap C) F
    (sigmaSiftedContinuous_canonicalColimits F · hC hF) G
  rw [hf, hg] at hm
  change IsSimplicialHomotopyEquivalence (pinchedHomMap
    (siftedContinuousFunctorInclusion (SigmaPresheafInfinity C) D ≫
      (pre (sigmaYonedaInfinityMap C)).app D) x y)
  rw [pinchedHomMap_comp]
  exact (siftedContinuousFunctorInclusion_isFullyFaithful (SigmaPresheafInfinity C) D x y).comp hm

end SerrePositivity.InfinityCategories.HomotopyLimits
