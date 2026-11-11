module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.RelativeRoofPullbackLift
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits SSet
open scoped _root_.Simplicial
variable {I E X Q : SSet.{u}} (r : E ⟶ Q) (q : X ⟶ Q)
variable (u : I ⟶ pullback r q) (b : (Δ[0] : SSet.{u}) ⟶ pullback r q)
/-- 元の Quillen A の全 slice は、同じ商側三角形への元の実屋根比較の厳密な引き戻し。 -/
lemma relativeRoofSquare_isPullback :
    IsPullback (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.relativeRoofTriangleMap r q u b) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.relativeRoofSourceMap r q u b)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sliceRoofTriangleMap r (u ≫ pullback.fst r q) (b ≫ pullback.fst r q))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.relativeRoofComparison r q u b) where
  w := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.relativeRoofSquare_comm r q u b
  isLimit' := ⟨PullbackCone.IsLimit.mk (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.relativeRoofSquare_comm r q u b)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.relativeRoofSquareLift r q u b)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.relativeRoofSquareLift_triangle r q u b) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.relativeRoofSquareLift_source r q u b)
    (by
      intro s m h₀ h₁
      apply pullback.hom_ext
      · rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.relativeRoofSquareLift, pullback.lift_fst]
        have h := congrArg (fun t => t ≫ pullback.fst
          (u ≫ pullback.fst r q) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (b ≫ pullback.fst r q))) h₀
        simpa only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.relativeRoofTriangleMap_fst] using! h
      · rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.relativeRoofSquareLift, pullback.lift_snd]
        apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.slicePullbackPostcomp_jointly_monic r q b
        · rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.relativeRoofConeLift_fst]
          have h := congrArg (fun t => t ≫ pullback.snd
            (u ≫ pullback.fst r q) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (b ≫ pullback.fst r q))) h₀
          simpa only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.relativeRoofTriangleMap_snd] using! h
        · rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.relativeRoofConeLift_snd]
          have h := congrArg (fun t => t ≫ pullback.fst
            (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (b ≫ pullback.snd r q)) (u ≫ pullback.snd r q)) h₁
          simpa only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.relativeRoofSourceMap_fst] using! h)⟩
end SerrePositivity.InfinityCategories.Project.DerivedCategories
