module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.FullSliceLift
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.RightFibrationMappingSpan

/-!
概要：全部分圏内の slice 引き戻しは、周囲の同じ二図式の slice 引き戻しと厳密に同型。
方針：周囲の錐の始点を元の図式で制限し、join 全体を全部分複体へ持ち上げる。
規約：元の図式への射影を厳密に保つ。
使われ方：Indκ の左 Kan 局所添字への小さい comma 模型の移送。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
variable {K A X : SSet.{u}} (P : X _⦋0⦌ → Prop)
  (δ : A ⟶ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P : SSet.{u}))
  (D : K ⟶ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P : SSet.{u}))
local notation "i" => SSet.Subcomplex.ι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P)
local notation "N" => pullback δ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection D)
local notation "Q" => pullback (δ ≫ i) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (D ≫ i))

/-- 全部分圏内の同じ錐を周囲へ含め、元の図式への射影を保つ。 -/
def fullSlicePullbackMap : N ⟶ Q :=
  pullback.lift (pullback.fst _ _)
    (pullback.snd _ _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverPostcomp D i) (by
      rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.sliceOverPostcomp_projection,
        ← Category.assoc, pullback.condition]
      simp only [Category.assoc])

/-- 周囲の錐の始点は元の図式の像なので、全部分圏の頂点条件を満たす。 -/
lemma fullSlicePullback_vertex (a : Q _⦋0⦌) :
    P ((pullback.snd (δ ≫ i) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (D ≫ i)) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (D ≫ i)).app (Opposite.op ⦋0⦌) a) := by
  rw [← pullback.condition]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex
    ((pullback.fst (δ ≫ i) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (D ≫ i)) ≫ δ).app (Opposite.op ⦋0⦌) a)

/-- 同じ周囲の錐の全族を全部分圏内へ戻す。 -/
def fullSlicePullbackInverse : Q ⟶ N :=
  pullback.lift (pullback.fst _ _)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.fullSliceLift P D (pullback.snd _ _) (fullSlicePullback_vertex P δ D)) (by
      apply (cancel_mono i).mp
      simp only [Category.assoc]
      rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.sliceOverPostcomp_projection]
      simp only [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.fullSliceLift_postcomp]
      simpa only [Category.assoc] using
        (pullback.condition (f := δ ≫ i) (g := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (D ≫ i))))

/-- 全部分圏内の同じ slice 引き戻しと周囲の引き戻しの厳密な同型。 -/
def fullSlicePullbackIso : N ≅ Q where
  hom := fullSlicePullbackMap P δ D
  inv := fullSlicePullbackInverse P δ D
  hom_inv_id := by
    apply pullback.hom_ext
    · simp only [fullSlicePullbackMap, fullSlicePullbackInverse, Category.assoc,
        pullback.lift_fst, Category.id_comp]
    · apply _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.fullSlicePostcomp_cancel P D
      simp only [Category.assoc, fullSlicePullbackInverse, pullback.lift_snd,
        _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.fullSliceLift_postcomp, fullSlicePullbackMap, Category.id_comp]
  inv_hom_id := by
    apply pullback.hom_ext
    · simp only [fullSlicePullbackMap, fullSlicePullbackInverse, Category.assoc,
        pullback.lift_fst, Category.id_comp]
    · simp only [fullSlicePullbackMap, fullSlicePullbackInverse, Category.assoc,
        pullback.lift_snd, pullback.lift_snd_assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.fullSliceLift_postcomp, Category.id_comp]

/-- 同じ同型は元の図式の始域への射影を厳密に保つ。 -/
lemma fullSlicePullbackIso_hom_fst :
    (fullSlicePullbackIso P δ D).hom ≫ pullback.fst _ _ = pullback.fst _ _ :=
  pullback.lift_fst _ _ _

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
