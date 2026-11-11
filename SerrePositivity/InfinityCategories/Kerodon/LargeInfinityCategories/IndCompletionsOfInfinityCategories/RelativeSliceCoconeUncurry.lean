module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.RelativeFunctorSpace
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.JoinTensor

/-!
概要：同じ底を固定した slice 関手の全族を、底と終点を固定した全余錐へ展開する。
方針：実相対評価と join・直積の比較を組み合わせる。
規約：固定条件は全次数の射の等式。使われ方：実補間の相対同型の uncurry。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
variable {A X : SSet.{u}} (p : (Δ[0] : SSet.{u}) ⟶ X) (b : A ⟶ X)
local notation "R" => _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection p) b

/-- 同じ底を固定した slice 関手の全相対評価を、パラメーターを左にして読む。 -/
def relativeSliceCoconeLeft : R ⊗ A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver p :=
  (β_ R A).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry (𝟙 R)

/-- 相対評価は、全パラメーターで同じ元の底図式を保つ。 -/
lemma relativeSliceCoconeLeft_projection :
    relativeSliceCoconeLeft p b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection p = snd R A ≫ b := by
  rw [relativeSliceCoconeLeft, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry_projection]
  rfl

/-- 全相対 slice 関手を、元の形状と全パラメーター上の全余錐へ展開する普遍族。 -/
def relativeSliceCoconeUncurry : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A (Δ[0] : SSet.{u}) ⊗ R ⟶ X :=
  (β_ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A Δ[0]) R).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinTensorLeft R A Δ[0] ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry (relativeSliceCoconeLeft p b)

/-- 普遍全余錐の底は、元の同じ図式に全パラメーターで厳密に固定される。 -/
lemma relativeSliceCoconeUncurry_old :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A (Δ[0] : SSet.{u}) ▷ R) ≫ relativeSliceCoconeUncurry p b = fst A R ≫ b := by
  have hs : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A (Δ[0] : SSet.{u}) ▷ R) ≫ (β_ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A Δ[0]) R).hom =
      (β_ A R).hom ≫ (R ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A Δ[0]) := by rfl
  rw [relativeSliceCoconeUncurry, ← Category.assoc, hs, Category.assoc,
    ← Category.assoc (R ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A Δ[0]), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinTensorLeft_inl,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.sliceOverUncurry_projection, relativeSliceCoconeLeft_projection,
    braiding_hom_snd_assoc]

/-- 普遍全余錐の頂点も、元の同じ指定点写像に全パラメーターで固定される。 -/
lemma relativeSliceCoconeUncurry_tip :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A (Δ[0] : SSet.{u}) ▷ R) ≫ relativeSliceCoconeUncurry p b = fst Δ[0] R ≫ p := by
  have hs : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A (Δ[0] : SSet.{u}) ▷ R) ≫ (β_ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A Δ[0]) R).hom =
      (β_ Δ[0] R).hom ≫ (R ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A Δ[0]) := by rfl
  rw [relativeSliceCoconeUncurry, ← Category.assoc, hs, Category.assoc,
    ← Category.assoc (R ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A Δ[0]), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinTensorLeft_inr,
    Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry_fixed, braiding_hom_snd_assoc]

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
