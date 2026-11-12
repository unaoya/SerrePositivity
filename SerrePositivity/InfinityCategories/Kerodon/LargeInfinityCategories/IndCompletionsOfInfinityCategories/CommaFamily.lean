module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.Shapes
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.SliceMap

/-!
概要：comma 上の全パラメータ族を、元の指定頂点への全余錐から構成する。
方針：slice の curry と厳密な引き戻しの普遍性を使う。
規約：全図式・全余錐を保持。使われ方：有限図式の filtered 表示の境界延長。

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

/-- 同じ始域図式と指定頂点への全余錐が定める comma の全パラメータ族。 -/
def commaFamilyLift {A B X : SSet.{u}} (δ : B ⟶ X) (x : X _⦋0⦌)
    (a : A ⟶ B) (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A (Δ[0] : SSet.{u}) ⟶ X)
    (hl : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A Δ[0] ≫ F = a ≫ δ)
    (hr : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A Δ[0] ≫ F = SSet.yonedaEquiv.symm x) : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanShape δ x :=
  pullback.lift a (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverCurry F hr) (by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.sliceOverCurry_projection]; exact hl.symm)

/-- 元の始域図式は厳密に回収される。 -/
lemma commaFamilyLift_projection {A B X : SSet.{u}} (δ : B ⟶ X) (x : X _⦋0⦌)
    (a : A ⟶ B) (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A (Δ[0] : SSet.{u}) ⟶ X) (hl) (hr) :
    commaFamilyLift δ x a F hl hr ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanProjection δ x = a :=
  pullback.lift_fst _ _ _

/-- 同じ族から読み戻した全余錐の射は、元の全射そのもの。 -/
lemma commaFamilyLift_uncurry {A B X : SSet.{u}} (δ : B ⟶ X) (x : X _⦋0⦌)
    (a : A ⟶ B) (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A (Δ[0] : SSet.{u}) ⟶ X) (hl) (hr) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry (commaFamilyLift δ x a F hl hr ≫
      pullback.snd δ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm x))) = F := by
  rw [commaFamilyLift, pullback.lift_snd, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry_curry]

/-- 元の任意の全 comma 族は、その始域図式と全余錐から厳密に再構成される。 -/
lemma commaFamilyLift_eta {A B X : SSet.{u}} (δ : B ⟶ X) (x : X _⦋0⦌)
    (q : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanShape δ x) :
    commaFamilyLift δ x (q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanProjection δ x)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry (q ≫ pullback.snd δ
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm x))))
      (by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.sliceOverUncurry_projection, Category.assoc, ← pullback.condition,
        ← Category.assoc]) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry_fixed _) = q := by
  apply pullback.hom_ext
  · exact commaFamilyLift_projection _ _ _ _ _ _
  · rw [commaFamilyLift, pullback.lift_snd, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverCurry_uncurry]

/-- 全族の持ち上げは任意のパラメータの制限と厳密に可換。 -/
lemma commaFamilyLift_precomp {A₀ A B X : SSet.{u}} (δ : B ⟶ X) (x : X _⦋0⦌)
    (a : A ⟶ B) (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A (Δ[0] : SSet.{u}) ⟶ X) (hl) (hr) (g : A₀ ⟶ A) :
    g ≫ commaFamilyLift δ x a F hl hr =
    commaFamilyLift δ x (g ≫ a) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap g (𝟙 Δ[0]) ≫ F)
      (by rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl_joinMap, Category.assoc, hl, ← Category.assoc])
      (by rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr_joinMap, Category.id_comp]; exact hr) := by
  apply pullback.hom_ext
  · rw [Category.assoc, commaFamilyLift_projection, commaFamilyLift_projection]
  · simp only [commaFamilyLift, Category.assoc, pullback.lift_snd]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverCurry_precomp F hr g

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
