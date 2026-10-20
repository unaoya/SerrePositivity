module
public import SerrePositivity.InfinityCategories.Derived.RelativeRoofPullbackLift
/-!
概要：右 Kan 比較の全 slice を、商側三角形への元の実屋根比較の厳密な引き戻しと同定する。
方針：二成分の全錐の実復元から普遍性を証明し、同じ二射影で一意性を検出する。
規約：圏のホモトピー圏だけの正方形ではない。使われ方：left cofinality の実基底変換。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits SSet
open scoped Simplicial
variable {I E X Q : SSet.{u}} (r : E ⟶ Q) (q : X ⟶ Q)
variable (u : I ⟶ pullback r q) (b : (Δ[0] : SSet.{u}) ⟶ pullback r q)
/-- 元の Quillen A の全 slice は、同じ商側三角形への元の実屋根比較の厳密な引き戻し。 -/
lemma relativeRoofSquare_isPullback :
    IsPullback (relativeRoofTriangleMap r q u b) (relativeRoofSourceMap r q u b)
      (sliceRoofTriangleMap r (u ≫ pullback.fst r q) (b ≫ pullback.fst r q))
      (relativeRoofComparison r q u b) where
  w := relativeRoofSquare_comm r q u b
  isLimit' := ⟨PullbackCone.IsLimit.mk (relativeRoofSquare_comm r q u b)
    (relativeRoofSquareLift r q u b)
    (relativeRoofSquareLift_triangle r q u b) (relativeRoofSquareLift_source r q u b)
    (by
      intro s m h₀ h₁
      apply pullback.hom_ext
      · rw [relativeRoofSquareLift, pullback.lift_fst]
        have h := congrArg (fun t => t ≫ pullback.fst
          (u ≫ pullback.fst r q) (sliceOverProjection (b ≫ pullback.fst r q))) h₀
        simpa only [Category.assoc, relativeRoofTriangleMap_fst] using! h
      · rw [relativeRoofSquareLift, pullback.lift_snd]
        apply slicePullbackPostcomp_jointly_monic r q b
        · rw [relativeRoofConeLift_fst]
          have h := congrArg (fun t => t ≫ pullback.snd
            (u ≫ pullback.fst r q) (sliceOverProjection (b ≫ pullback.fst r q))) h₀
          simpa only [Category.assoc, relativeRoofTriangleMap_snd] using! h
        · rw [relativeRoofConeLift_snd]
          have h := congrArg (fun t => t ≫ pullback.fst
            (sliceOverProjection (b ≫ pullback.snd r q)) (u ≫ pullback.snd r q)) h₁
          simpa only [Category.assoc, relativeRoofSourceMap_fst] using! h)⟩
end SerrePositivity.InfinityCategories
