module
public import SerrePositivity.InfinityCategories.Stable.ArrowPullbackDiagonal
public import SerrePositivity.InfinityCategories.Stable.ExcisionPullbackComparisonFamily

/-!
概要：実比較正方形の対角辺を保ったまま、同じ cospan の普遍錐を構成する。
方針：端点で可逆なホモトピーによる矢印圏の同値と、厳密な錐の輸送を使う。
規約：一般安定性を仮定しない。使われ方：切除判定の第二条件と実 θ の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

lemma exists_excisionArrowPullbackSquare_diagonal {X : SSet.{u}} [Quasicategory X]
    [HasFiniteLimits X] {F : nerve ExcisionGridIndex.{u} ⟶ X}
    (c : JoinCone (nerveMap (posetSubtypeInclusion IsExcisionFullPunctured) ≫ F))
    (hc : IsLimitCone c)
    (d : JoinCone (pullbackCospan (excisionRawSuspensionSquare (excisionReplaceInitial c))))
    (hd : IsLimitCone d)
    (e : JoinCone (pullbackCospan (excisionPullbackComparisonFamily c d hd)))
    (he : IsLimitCone e) :
    ∃ R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ (ihom (Δ[1] : SSet.{u})).obj X,
      pullbackCospan R = pullbackCospan (excisionPullbackComparisonFamily c d hd) ∧
      IsPullbackSquare R ∧ squareVertex R 0 0 = functorVertex (SSet.yonedaEquiv.symm
        (squareDiagonalArrow (uncurry (SSet.yonedaEquiv.symm
          (functorPullbackComparisonEdge (excisionPullbackComparisonFamily c d hd)
            e he).edge))).edge) :=
  exists_arrowPullbackSquare_diagonal _ e he
    (excisionPullbackComparisonFamily_source_isPullback c hc d hd)

end SerrePositivity.InfinityCategories
