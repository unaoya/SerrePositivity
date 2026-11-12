module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.RelativeRoofBaseChange
/-!
概要：実屋根比較の正方形に整合する二図式を、元の Quillen A の全 slice へ持ち上げる。
方針：二成分の全錐を先に復元し、同じ実添字への射影の一致を証明する。
規約：高次の全錐を保持。使われ方：右 Kan 比較の slice の厳密 pullback の普遍性。
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
variable (s : PullbackCone
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sliceRoofTriangleMap r (u ≫ pullback.fst r q) (b ≫ pullback.fst r q))
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.relativeRoofComparison r q u b))
/-- 比較正方形に整合する二図式は、元の同じ実添字を持つ。 -/
lemma relativeRoofCone_index : s.fst ≫ pullback.fst _ _ = s.snd ≫ pullback.snd _ _ := by
  have h := congrArg (fun t => t ≫ pullback.snd
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection ((b ≫ pullback.fst r q) ≫ r)) ((u ≫ pullback.fst r q) ≫ r))
      s.condition
  simpa only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sliceRoofTriangleMap_snd, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.relativeRoofComparison_snd] using! h
/-- 比較正方形に整合する二図式は、同じ底を持つ二成分の実全錐を与える。 -/
def relativeRoofConeFamily : s.pt ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.slicePullbackDiagram r q b :=
  pullback.lift (s.fst ≫ pullback.snd _ _) (s.snd ≫ pullback.fst _ _) (by
    have h := congrArg (fun t => t ≫ pullback.fst
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection ((b ≫ pullback.fst r q) ≫ r)) ((u ≫ pullback.fst r q) ≫ r))
        s.condition
    simpa only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sliceRoofTriangleMap_fst, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.relativeRoofComparison_fst] using! h)
/-- 整合する二成分の全錐から、元の引き戻し圏の同じ一つの全錐を復元する。 -/
def relativeRoofConeLift : s.pt ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver b :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.slicePullbackBackwardFamily r q b (relativeRoofConeFamily r q u b s)
/-- 復元した全錐の E 成分は元の全錐そのもの。 -/
lemma relativeRoofConeLift_fst :
    relativeRoofConeLift r q u b s ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverPostcomp b (pullback.fst r q) =
      s.fst ≫ pullback.snd _ _ := by
  rw [relativeRoofConeLift, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.slicePullbackBackwardFamily_fst, relativeRoofConeFamily,
    pullback.lift_fst]
/-- 復元した全錐の X 成分も元の全錐そのもの。 -/
lemma relativeRoofConeLift_snd :
    relativeRoofConeLift r q u b s ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverPostcomp b (pullback.snd r q) =
      s.snd ≫ pullback.fst _ _ := by
  rw [relativeRoofConeLift, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.slicePullbackBackwardFamily_snd, relativeRoofConeFamily,
    pullback.lift_snd]
/-- 復元した全錐は、指定した元の実添字図式と厳密に重なる。 -/
lemma relativeRoofConeLift_projection :
    (s.fst ≫ pullback.fst _ _) ≫ u = relativeRoofConeLift r q u b s ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection b := by
  apply pullback.hom_ext
  · calc
      _ = s.fst ≫ (pullback.fst _ _ ≫ (u ≫ pullback.fst r q)) := by
        simp only [Category.assoc]
      _ = s.fst ≫ (pullback.snd _ _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (b ≫ pullback.fst r q)) :=
        congrArg (fun t => s.fst ≫ t) (pullback.condition (f := u ≫ pullback.fst r q)
          (g := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (b ≫ pullback.fst r q)))
      _ = (relativeRoofConeLift r q u b s ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverPostcomp b (pullback.fst r q)) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (b ≫ pullback.fst r q) := by
        rw [relativeRoofConeLift_fst, Category.assoc]
      _ = _ := by rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.sliceOverPostcomp_projection, Category.assoc]
  · calc
      _ = (s.fst ≫ pullback.fst _ _) ≫ (u ≫ pullback.snd r q) := Category.assoc _ _ _
      _ = (s.snd ≫ pullback.snd _ _) ≫ (u ≫ pullback.snd r q) :=
        congrArg (fun t => t ≫ (u ≫ pullback.snd r q)) (relativeRoofCone_index r q u b s)
      _ = s.snd ≫ (pullback.fst _ _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (b ≫ pullback.snd r q)) :=
        (Category.assoc _ _ _).trans (congrArg (fun t => s.snd ≫ t)
          (pullback.condition (f := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (b ≫ pullback.snd r q))
            (g := u ≫ pullback.snd r q)).symm)
      _ = (relativeRoofConeLift r q u b s ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverPostcomp b (pullback.snd r q)) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (b ≫ pullback.snd r q) := by
        rw [relativeRoofConeLift_snd, Category.assoc]
      _ = _ := by rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.sliceOverPostcomp_projection, Category.assoc]
/-- 比較正方形の二つの全図式を、元の同じ Quillen A の実 slice に持ち上げる。 -/
def relativeRoofSquareLift : s.pt ⟶ pullback u (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection b) :=
  pullback.lift (s.fst ≫ pullback.fst _ _) (relativeRoofConeLift r q u b s)
    (relativeRoofConeLift_projection r q u b s)
/-- 持ち上げの E 側三角形は、元の全図式に厳密に一致する。 -/
lemma relativeRoofSquareLift_triangle :
    relativeRoofSquareLift r q u b s ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.relativeRoofTriangleMap r q u b = s.fst := by
  apply pullback.hom_ext
  · rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.relativeRoofTriangleMap_fst, relativeRoofSquareLift, pullback.lift_fst]
  · rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.relativeRoofTriangleMap_snd, ← Category.assoc,
      relativeRoofSquareLift, pullback.lift_snd, relativeRoofConeLift_fst]
/-- 持ち上げの X 側屋根も、元の全図式に厳密に一致する。 -/
lemma relativeRoofSquareLift_source :
    relativeRoofSquareLift r q u b s ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.relativeRoofSourceMap r q u b = s.snd := by
  apply pullback.hom_ext
  · rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.relativeRoofSourceMap_fst, ← Category.assoc,
      relativeRoofSquareLift, pullback.lift_snd, relativeRoofConeLift_snd]
  · rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.relativeRoofSourceMap_snd, relativeRoofSquareLift, pullback.lift_fst]
    exact relativeRoofCone_index r q u b s
end SerrePositivity.InfinityCategories.Project.DerivedCategories
