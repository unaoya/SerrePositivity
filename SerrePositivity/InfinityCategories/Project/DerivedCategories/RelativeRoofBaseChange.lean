module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.SlicePullbackIso
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.SliceRoofCorner
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.SliceProjectionLaws
/-!
概要：引き戻し圏への実図式に付随する、元の屋根・標的屋根・全三角形の比較正方形を作る。
方針：同じ二つの射影を保持し、slice の固定図式の等式輸送を明示する。
規約：全錐の高次単体を保存。使われ方：右 Kan 比較の Quillen A の実 slice の基底変換表示。
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
/-- 元の同じ始域から指定対象への実分子を持つ屋根。 -/
def relativeRoofOriginal : SSet.{u} :=
  pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (b ≫ pullback.snd r q)) (u ≫ pullback.snd r q)
/-- 元の屋根から、同じ添字と標的の実分子を持つ標的屋根への写像。 -/
def relativeRoofComparison : relativeRoofOriginal r q u b ⟶
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sliceRoofTarget r (u ≫ pullback.fst r q) (b ≫ pullback.fst r q) :=
  pullback.lift (pullback.fst _ _ ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.slicePullbackRightMap r q b) (pullback.snd _ _) (by
    calc
      _ = pullback.fst _ _ ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.slicePullbackRightMap r q b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection _) :=
        Category.assoc _ _ _
      _ = pullback.fst _ _ ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (b ≫ pullback.snd r q) ≫ q) :=
        congrArg (fun t => pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (b ≫ pullback.snd r q))
          (u ≫ pullback.snd r q) ≫ t) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.slicePullbackRightMap_projection r q b)
      _ = (pullback.fst _ _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (b ≫ pullback.snd r q)) ≫ q :=
        (Category.assoc _ _ _).symm
      _ = (pullback.snd _ _ ≫ (u ≫ pullback.snd r q)) ≫ q :=
        congrArg (fun t => t ≫ q) (pullback.condition (f :=
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (b ≫ pullback.snd r q)) (g := u ≫ pullback.snd r q))
      _ = pullback.snd _ _ ≫ ((u ≫ pullback.fst r q) ≫ r) :=
        (Category.assoc _ _ _).trans (congrArg (fun t => pullback.snd
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (b ≫ pullback.snd r q)) (u ≫ pullback.snd r q) ≫ t)
            (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.slicePullbackPoint_comm r q u).symm))
/-- 元の屋根比較は全分子を同じ底へ送る。 -/
lemma relativeRoofComparison_fst : relativeRoofComparison r q u b ≫ pullback.fst _ _ =
    pullback.fst _ _ ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.slicePullbackRightMap r q b := pullback.lift_fst _ _ _
/-- 元の屋根比較は元の同じ全添字を固定する。 -/
lemma relativeRoofComparison_snd : relativeRoofComparison r q u b ≫ pullback.snd _ _ =
    pullback.snd _ _ := pullback.lift_snd _ _ _
/-- 元の引き戻し圏の全 slice から、E 内の同じ指定対象への全三角形への写像。 -/
def relativeRoofTriangleMap :
    pullback u (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection b) ⟶
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sliceRoofTriangle (u ≫ pullback.fst r q) (b ≫ pullback.fst r q) :=
  pullback.lift (pullback.fst _ _)
    (pullback.snd _ _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverPostcomp b (pullback.fst r q)) (by
      rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.sliceOverPostcomp_projection, ← Category.assoc,
        pullback.condition, Category.assoc])
/-- 全三角形の元の添字への射影。 -/
lemma relativeRoofTriangleMap_fst : relativeRoofTriangleMap r q u b ≫ pullback.fst _ _ =
    pullback.fst _ _ := pullback.lift_fst _ _ _
/-- 全三角形の E 内の元の全錐への射影。 -/
lemma relativeRoofTriangleMap_snd : relativeRoofTriangleMap r q u b ≫ pullback.snd _ _ =
    pullback.snd _ _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverPostcomp b (pullback.fst r q) := pullback.lift_snd _ _ _
/-- 元の引き戻し圏の全 slice から、同じ X 内の分子を持つ元の屋根への写像。 -/
def relativeRoofSourceMap : pullback u (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection b) ⟶ relativeRoofOriginal r q u b :=
  pullback.lift (pullback.snd _ _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverPostcomp b (pullback.snd r q))
    (pullback.fst _ _) (by
      rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.sliceOverPostcomp_projection, ← Category.assoc,
        ← pullback.condition, Category.assoc])
/-- 元の全 slice の屋根表示の分子。 -/
lemma relativeRoofSourceMap_fst : relativeRoofSourceMap r q u b ≫ pullback.fst _ _ =
    pullback.snd _ _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverPostcomp b (pullback.snd r q) := pullback.lift_fst _ _ _
/-- 元の全 slice の屋根表示の添字。 -/
lemma relativeRoofSourceMap_snd : relativeRoofSourceMap r q u b ≫ pullback.snd _ _ =
    pullback.fst _ _ := pullback.lift_snd _ _ _
/-- 全三角形の標的屋根表示と元の屋根比較は、全高次単体で厳密に可換。 -/
lemma relativeRoofSquare_comm :
    relativeRoofTriangleMap r q u b ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sliceRoofTriangleMap r (u ≫ pullback.fst r q) (b ≫ pullback.fst r q) =
        relativeRoofSourceMap r q u b ≫ relativeRoofComparison r q u b := by
  apply pullback.hom_ext
  · rw [Category.assoc (relativeRoofTriangleMap r q u b), _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sliceRoofTriangleMap_fst,
      ← Category.assoc (relativeRoofTriangleMap r q u b), relativeRoofTriangleMap_snd,
      Category.assoc (relativeRoofSourceMap r q u b), relativeRoofComparison_fst,
      ← Category.assoc (relativeRoofSourceMap r q u b), relativeRoofSourceMap_fst]
    simpa only [Category.assoc] using! congrArg
      (fun t => pullback.snd u (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection b) ≫ t) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.slicePullbackPostcomp_comm r q b)
  · rw [Category.assoc (relativeRoofTriangleMap r q u b), _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sliceRoofTriangleMap_snd,
      relativeRoofTriangleMap_fst, Category.assoc (relativeRoofSourceMap r q u b),
      relativeRoofComparison_snd, relativeRoofSourceMap_snd]
end SerrePositivity.InfinityCategories.Project.DerivedCategories
