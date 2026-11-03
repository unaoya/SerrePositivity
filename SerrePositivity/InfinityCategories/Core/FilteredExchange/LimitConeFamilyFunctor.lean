module

public import SerrePositivity.InfinityCategories.Core.ConeFamily
public import SerrePositivity.InfinityCategories.Core.Equivalence
public import SerrePositivity.InfinityCategories.Core.EquivalencePath
public import SerrePositivity.InfinityCategories.Core.FunctorEvaluation
public import SerrePositivity.InfinityCategories.Core.FunctorLimits
public import SerrePositivity.InfinityCategories.Core.FunctorPointwiseLimitCriterion
public import SerrePositivity.InfinityCategories.Core.InternalHomFlipAdjunction
public import SerrePositivity.InfinityCategories.Core.InternalHomFlipVertices
public import SerrePositivity.InfinityCategories.Core.Join
public import SerrePositivity.InfinityCategories.Core.Limit
public import SerrePositivity.InfinityCategories.Core.FilteredExchange.FunctorVertexCone
public import SerrePositivity.InfinityCategories.Core.FilteredExchange.LimitConeFamilyReadback

/-!
概要：coherent な極限錐の族を、元の関手 ∞ 圏の極限錐として読む。
方針：二変数を交換し、元の全錐の各評価との等号で点ごとの極限判定を適用する。
規約：元の族とその頂点関手を保持。使われ方：部分極限の族と有限積の交換の接続。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の錐の族を二変数交換して得る関手圏内の全錐。 -/
def pointwiseLimitFamilyCone {B K X : SSet.{u}}
    (q : B ⟶ (ihom (join (Δ[0] : SSet.{u}) K)).obj X) :
    JoinCone (internalHomFlipHomEquiv B K X (q ≫ coneRestriction K X)) :=
  ⟨internalHomFlipHomEquiv B (join (Δ[0] : SSet.{u}) K) X q,
    (internalHomFlipHomEquiv_pre_app (joinInr Δ[0] K) q).symm⟩

/-- 関手圏の全錐の評価は、元の各点の錐と同じ極限性を持つ。 -/
lemma pointwiseLimitFamilyCone_evaluate_iff {B K X : SSet.{u}}
    (q : B ⟶ (ihom (join (Δ[0] : SSet.{u}) K)).obj X) (b : B _⦋0⦌) :
    IsLimitCone (evaluateFunctorCone (pointwiseLimitFamilyCone q) b) ↔
      IsLimitCone (functorVertexCone (q.app (Opposite.op ⦋0⦌) b)) := by
  let T := join (Δ[0] : SSet.{u}) K
  have hflip : internalHomFlipHomEquiv T B X (internalHomFlipHomEquiv B T X q) = q :=
    (internalHomFlipHomEquiv B T X).left_inv q
  have h := internalHomFlipHomEquiv_app_zero (internalHomFlipHomEquiv B T X q) b
  rw [hflip] at h
  have he : functorVertexConeMap (q.app (Opposite.op ⦋0⦌) b) =
      (evaluateFunctorCone (pointwiseLimitFamilyCone q) b).val := by
    rw [h]
    exact (functorVertexEquiv _ _).symm_apply_apply _
  exact (isLimitCone_functorVertexCone_iff_of_val _ _ he).symm

/-- 各点が極限錐なら、元の族の二変数交換は関手 ∞ 圏で極限錐。 -/
lemma pointwiseLimitFamilyCone_isLimit {B K X : SSet.{u}} [Quasicategory X]
    (q : B ⟶ (ihom (join (Δ[0] : SSet.{u}) K)).obj X)
    (hq : ∀ b : B _⦋0⦌, IsLimitCone (functorVertexCone (q.app (Opposite.op ⦋0⦌) b))) :
    IsLimitCone (pointwiseLimitFamilyCone q) :=
  isLimitCone_of_pointwise _ (fun b => (pointwiseLimitFamilyCone_evaluate_iff q b).mpr (hq b))

/-- 元の関手錐の頂点は、元の錐族の頂点評価関手そのもの。 -/
lemma pointwiseLimitFamilyCone_vertex {B K X : SSet.{u}}
    (q : B ⟶ (ihom (join (Δ[0] : SSet.{u}) K)).obj X) :
    (pointwiseLimitFamilyCone q).vertex = functorVertex
      (q ≫ evaluateFunctorAt (SSet.yonedaEquiv (joinInl (Δ[0] : SSet.{u}) K))) := by
  rw [JoinCone.vertex_eq, SSet.yonedaEquiv_comp]
  exact internalHomFlipHomEquiv_app_zero q _

end SerrePositivity.InfinityCategories.F2
