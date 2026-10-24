module

public import SerrePositivity.InfinityCategories.F2.Ind.IndContinuousLeftKan
public import SerrePositivity.InfinityCategories.F2.Ind.ContinuousFunctorRestriction
public import SerrePositivity.InfinityCategories.F1B.KanExtension.LeftCanonicalMapping

/-!
概要：小さい κ-filtered 余極限を保つ関手の元の Yoneda 制限射は充満忠実。
方針：保存関手の標準局所 Kan 条件を、実際の pinched 写像空間比較へ適用する。
規約：指定の制限射そのものの全写像空間を扱い、追加の instance 仮定を入れない。
使われ方：HTT 5.3.5.10 の普遍性の充満忠実性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable (κ : Cardinal.{u}) [Fact κ.IsRegular] (C : SSet.{u}) [Quasicategory C]
  (D : SSet.{u + 1}) [Quasicategory D]

/-- 元の保存関手の全部分 ∞ 圏からの、元の Yoneda 制限射自体が充満忠実。 -/
lemma indKappaContinuousRestriction_isFullyFaithful :
    IsFullyFaithful (indKappaContinuousRestriction κ C D) := by
  intro x y
  let F := (functorVertexEquiv (IndInfinity κ C) D).symm x.val
  let G := (functorVertexEquiv (IndInfinity κ C) D).symm y.val
  have hF : PreservesSmallKappaFilteredColimits κ F := fullSubcomplexOnVertices_vertex x
  have hf : functorVertex F = x.val := (functorVertexEquiv _ _).apply_symm_apply _
  have hg : functorVertex G = y.val := (functorVertexEquiv _ _).apply_symm_apply _
  have hm := F1B.kanLeftCanonical_pinchedHomMap_equivalence (indYoneda κ C) F
    (indContinuous_canonicalColimits κ F · hF) G
  rw [hf, hg] at hm
  change IsSimplicialHomotopyEquivalence (pinchedHomMap
    (kappaContinuousFunctorInclusion κ (IndInfinity κ C) D ≫ (pre (indYoneda κ C)).app D) x y)
  rw [pinchedHomMap_comp]
  exact (kappaContinuousFunctorInclusion_isFullyFaithful κ (IndInfinity κ C) D x y).comp hm

end SerrePositivity.InfinityCategories.F2.Ind
