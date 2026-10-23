module

public import SerrePositivity.InfinityCategories.F2.CatInfinity.ExactFunctorSpanCospanPreservation
public import SerrePositivity.InfinityCategories.F2.CatInfinity.LaxPullbackConeComponentCriterion
public import SerrePositivity.InfinityCategories.F2.CatInfinity.LaxPullbackCoconeComponentCriterion

/-!
概要：安定圏間の完全関手の lax pullback の四角形を両入力から判定する十分条件。
方針：完全性から元の span・cospan の錐の保存を導き、成分の普遍性を全体へ戻す。
規約：lax pullback 自身の安定性や射影の保存は仮定しない。
使われ方：零角の四角形の fiber/cofiber 条件の比較。
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

/-- 概要：両入力が引き戻し四角形なら元の lax pullback 内の四角形も引き戻し。
方針：完全関手による cospan 極限の保存から全体の極限性を導く。
規約：lax pullback の有限極限の存在は仮定しない。
使われ方：fiber 列と cofiber 列の成分からの回収。 -/
lemma isPullbackSquare_laxPullback_of_components
    (R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ laxPullback p q)
    (ha : IsPullbackSquare (R ≫ laxPullbackFst p q))
    (hb : IsPullbackSquare (R ≫ laxPullbackSnd p q)) : IsPullbackSquare R := by
  have hca := (isLimitCone_map_pullbackCone_iff (laxPullbackFst p q) R).2 ha
  have hcb := (isLimitCone_map_pullbackCone_iff (laxPullbackSnd p q) R).2 hb
  exact isLimitCone_laxPullback_of_components p q (pullbackCone R) hca hcb
    (exactFunctor_preserves_cospan_limit p _ hca) (exactFunctor_preserves_cospan_limit q _ hcb)

/-- 概要：両入力が押し出し四角形なら元の lax pullback 内の四角形も押し出し。
方針：完全関手による span 余極限の保存から全体の余極限性を導く。
規約：入力と標的の実際の完全性だけを使う。
使われ方：cofiber の成分ごとの普遍性。 -/
lemma isPushoutSquare_laxPullback_of_components
    (R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ laxPullback p q)
    (ha : IsPushoutSquare (R ≫ laxPullbackFst p q))
    (hb : IsPushoutSquare (R ≫ laxPullbackSnd p q)) : IsPushoutSquare R := by
  have hca := (isColimitCone_post_pushoutCocone_iff (laxPullbackFst p q) R).2 ha
  have hcb := (isColimitCone_post_pushoutCocone_iff (laxPullbackSnd p q) R).2 hb
  exact isColimitCone_laxPullback_of_components p q (pushoutCocone R) hca hcb
    (exactFunctor_preserves_span_colimit p _ hca) (exactFunctor_preserves_span_colimit q _ hcb)

end SerrePositivity.InfinityCategories.F2
