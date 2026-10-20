module
public import SerrePositivity.InfinityCategories.Derived.SliceCornerRightFibration
/-!
概要：全添字の商側三角形から同じ商屋根への写像を、相対 slice corner の引き戻しとして表示する。
方針：二つの全錐と実始域の射影で pullback の普遍性を直接検証する。
規約：全次数の厳密な図式。使われ方：実屋根の left cofinal 比較を引き戻す右ファイブレーション。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits SSet
open scoped Simplicial
variable {I E Q : SSet.{u}} (r : E ⟶ Q) (a : I ⟶ E) (p : (Δ[0] : SSet.{u}) ⟶ E)
/-- 元の全添字上の、指定頂点への全実三角形。 -/
def sliceRoofTriangle : SSet.{u} := pullback a (sliceOverProjection p)
/-- 同じ全添字上の、標的内の実屋根。 -/
def sliceRoofTarget : SSet.{u} := pullback (sliceOverProjection (p ≫ r)) (a ≫ r)
/-- 三角形から、同じ実分子と元の添字を持つ標的屋根への写像。 -/
def sliceRoofTriangleMap : sliceRoofTriangle a p ⟶ sliceRoofTarget r a p :=
  pullback.lift (pullback.snd _ _ ≫ sliceOverPostcomp p r) (pullback.fst _ _) (by
    rw [Category.assoc, F1B.kanSliceOverPostcomp_projection, ← Category.assoc,
      ← pullback.condition, Category.assoc])
/-- 標的屋根の実分子と元の始域を、相対 slice corner へ写す。 -/
def sliceRoofCornerBase : sliceRoofTarget r a p ⟶ sliceOverCorner p r :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ a) (by
    rw [Category.assoc]
    exact pullback.condition)
/-- 三角形の商屋根表示の元の添字。 -/
lemma sliceRoofTriangleMap_snd :
    sliceRoofTriangleMap r a p ≫ pullback.snd _ _ = pullback.fst a (sliceOverProjection p) :=
  pullback.lift_snd _ _ _
/-- 三角形の商屋根表示の実分子。 -/
lemma sliceRoofTriangleMap_fst :
    sliceRoofTriangleMap r a p ≫ pullback.fst _ _ =
      pullback.snd a (sliceOverProjection p) ≫ sliceOverPostcomp p r :=
  pullback.lift_fst _ _ _
/-- corner の底表示の実分子。 -/
lemma sliceRoofCornerBase_fst :
    sliceRoofCornerBase r a p ≫ pullback.fst _ _ =
      pullback.fst (sliceOverProjection (p ≫ r)) (a ≫ r) := pullback.lift_fst _ _ _
/-- corner の底表示の元の始域。 -/
lemma sliceRoofCornerBase_snd :
    sliceRoofCornerBase r a p ≫ pullback.snd _ _ =
      pullback.snd (sliceOverProjection (p ≫ r)) (a ≫ r) ≫ a := pullback.lift_snd _ _ _
/-- 商側三角形の全図式は、相対 slice corner と厳密に可換。 -/
lemma sliceRoofCorner_comm :
    pullback.snd a (sliceOverProjection p) ≫ sliceOverCornerMap p r =
      sliceRoofTriangleMap r a p ≫ sliceRoofCornerBase r a p := by
  apply pullback.hom_ext
  · rw [Category.assoc, sliceOverCornerMap, pullback.lift_fst,
      Category.assoc, sliceRoofCornerBase_fst, sliceRoofTriangleMap_fst]
  · rw [Category.assoc, sliceOverCornerMap, pullback.lift_snd,
      Category.assoc, sliceRoofCornerBase_snd, ← Category.assoc, sliceRoofTriangleMap_snd]
    exact (pullback.condition (f := a) (g := sliceOverProjection p)).symm
/-- corner と整合する二つの実図式の、元の始域での一致。 -/
lemma sliceRoofCorner_lift_condition {S : SSet.{u}} (k : S ⟶ sliceOver p)
    (l : S ⟶ sliceRoofTarget r a p)
    (h : k ≫ sliceOverCornerMap p r = l ≫ sliceRoofCornerBase r a p) :
    (l ≫ pullback.snd _ _) ≫ a = k ≫ sliceOverProjection p := by
  have hh := congrArg (fun t => t ≫ pullback.snd (sliceOverProjection (p ≫ r)) r) h
  simpa only [Category.assoc, sliceOverCornerMap, sliceRoofCornerBase,
    pullback.lift_snd] using hh.symm
/-- 商側三角形から商屋根への写像は、実相対 slice corner の厳密な引き戻し。 -/
lemma sliceRoofCorner_isPullback : IsPullback (pullback.snd a (sliceOverProjection p))
    (sliceRoofTriangleMap r a p) (sliceOverCornerMap p r) (sliceRoofCornerBase r a p) where
  w := sliceRoofCorner_comm r a p
  isLimit' := ⟨PullbackCone.IsLimit.mk (sliceRoofCorner_comm r a p)
    (fun s => pullback.lift (s.snd ≫ pullback.snd _ _) s.fst
      (sliceRoofCorner_lift_condition r a p s.fst s.snd s.condition))
    (fun _ => pullback.lift_snd _ _ _)
    (by
      intro s
      apply pullback.hom_ext
      · change (pullback.lift _ _ _ ≫ sliceRoofTriangleMap r a p) ≫ pullback.fst _ _ = _
        rw [Category.assoc, sliceRoofTriangleMap, pullback.lift_fst,
          ← Category.assoc, pullback.lift_snd]
        have hh := congrArg (fun t => t ≫ pullback.fst (sliceOverProjection (p ≫ r)) r)
          s.condition
        simpa only [Category.assoc, sliceOverCornerMap, sliceRoofCornerBase,
          pullback.lift_fst] using hh
      · rw [Category.assoc, sliceRoofTriangleMap, pullback.lift_snd, pullback.lift_fst])
    (by
      intro s m h₀ h₁
      apply pullback.hom_ext
      · rw [pullback.lift_fst]
        have hh := congrArg (fun t => t ≫ pullback.snd _ _) h₁
        simpa only [Category.assoc, sliceRoofTriangleMap, pullback.lift_snd] using hh
      · rw [pullback.lift_snd]
        exact h₀)⟩
/-- inner fibration の全添字の商側三角形から商屋根への写像は右ファイブレーション。 -/
instance sliceRoofTriangleMap_rightFibration [InnerFibration r] :
    RightFibration (sliceRoofTriangleMap r a p) :=
  ⟨rightFibrations.of_isPullback (sliceRoofCorner_isPullback r a p)
    (RightFibration.mem (p := sliceOverCornerMap p r))⟩
end SerrePositivity.InfinityCategories
