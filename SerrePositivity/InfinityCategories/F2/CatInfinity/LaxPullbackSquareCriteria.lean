module

public import SerrePositivity.InfinityCategories.F2.CatInfinity.ExactFunctorSpanCospanPreservation
public import SerrePositivity.InfinityCategories.F2.CatInfinity.LaxPullbackLimitCriterion
public import SerrePositivity.InfinityCategories.F2.CatInfinity.LaxPullbackColimitCriterion

/-!
概要：安定圏間の完全関手の lax pullback の四角形の成分判定。
方針：指定図式での入力の存在と、完全性から導く span・cospan の保存を使う。
規約：全有限極限の存在や lax pullback の安定性は仮定しない。
使われ方：零角の四角形の双カルテジアン性と射影の完全性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

variable {A B C : SSet.{u}} [Quasicategory A] [Quasicategory B] [Quasicategory C]
variable [IsStable A] [IsStable B] [IsStable C] (p : A ⟶ C) (q : B ⟶ C)
variable [IsExactFunctor p] [IsExactFunctor q]

/-- 概要：入力の cospan が極限を持つ四角形の引き戻し性は両入力で判定できる。
方針：完全関手の cospan 極限の保存と元の四角形の錐の一致を合成する。
規約：必要な二つの入力図式の存在だけを仮定する。
使われ方：fiber 四角形の成分判定。 -/
lemma isPullbackSquare_laxPullback_iff_of_input_limits
    (R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ laxPullback p q)
    (ha : HasLimit (pullbackCospan R ≫ laxPullbackFst p q))
    (hb : HasLimit (pullbackCospan R ≫ laxPullbackSnd p q)) :
    IsPullbackSquare R ↔ IsPullbackSquare (R ≫ laxPullbackFst p q) ∧
      IsPullbackSquare (R ≫ laxPullbackSnd p q) := by
  exact (isLimitCone_laxPullback_iff_components p q (pullbackCospan R) ha hb
    (fun c hc ↦ exactFunctor_preserves_cospan_limit p c hc)
    (fun c hc ↦ exactFunctor_preserves_cospan_limit q c hc) (pullbackCone R)).trans
    (and_congr (isLimitCone_map_pullbackCone_iff (laxPullbackFst p q) R)
      (isLimitCone_map_pullbackCone_iff (laxPullbackSnd p q) R))

/-- 概要：入力の span が余極限を持つ四角形の押し出し性は両入力で判定できる。
方針：完全関手の span 余極限の保存と元の四角形の余錐の一致を合成する。
規約：元の二つの入力図式の存在を明示する。
使われ方：cofiber 四角形の成分判定と両射影の保存。 -/
lemma isPushoutSquare_laxPullback_iff_of_input_colimits
    (R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ laxPullback p q)
    (ha : HasColimit (pushoutSpan R ≫ laxPullbackFst p q))
    (hb : HasColimit (pushoutSpan R ≫ laxPullbackSnd p q)) :
    IsPushoutSquare R ↔ IsPushoutSquare (R ≫ laxPullbackFst p q) ∧
      IsPushoutSquare (R ≫ laxPullbackSnd p q) := by
  exact (isColimitCone_laxPullback_iff_components p q (pushoutSpan R) ha hb
    (fun c hc ↦ exactFunctor_preserves_span_colimit p c hc)
    (fun c hc ↦ exactFunctor_preserves_span_colimit q c hc) (pushoutCocone R)).trans
    (and_congr (isColimitCone_post_pushoutCocone_iff (laxPullbackFst p q) R)
      (isColimitCone_post_pushoutCocone_iff (laxPullbackSnd p q) R))

end SerrePositivity.InfinityCategories.F2
