module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.Shapes

/-!
概要：既存の標準右Kan錐の内部の形状写像を固定し、その両因子への制限を表示する。
方針：同じcosliceのuncurryの固定条件と射影条件を使う。
規約：HTT §4.3.2、Kerodon §7.3（Tag 02Y1）の既存標準錐の計算法則。
使われ方：S8 の指定大域比較の前合成と、元の指定余単位との両立を照合する。
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

/-- 元のrightKanCanonicalConeの本文に現れる同じ形状写像。選択は追加しない。 -/
def rightKanCanonicalShape {K C : SSet.{u}} (δ : K ⟶ C) (c : C _⦋0⦌) :
    join (Δ[0] : SSet.{u}) (rightKanShape δ c) ⟶ C :=
  sliceUnderUncurry (pullback.fst (sliceUnderProjection (SSet.yonedaEquiv.symm c)) δ)

/-- 同じ標準形状の図式側の制限は、元の射影と添字写像の合成。 -/
lemma rightKanCanonicalShape_inr {K C : SSet.{u}} (δ : K ⟶ C) (c : C _⦋0⦌) :
    joinInr (Δ[0] : SSet.{u}) (rightKanShape δ c) ≫ rightKanCanonicalShape δ c =
      rightKanProjection δ c ≫ δ := by
  rw [rightKanCanonicalShape, sliceUnderUncurry_projection, pullback.condition]

/-- 同じ標準形状の頂点側の制限は、元の指定頂点の一点表示。 -/
lemma rightKanCanonicalShape_inl {K C : SSet.{u}} (δ : K ⟶ C) (c : C _⦋0⦌) :
    joinInl (Δ[0] : SSet.{u}) (rightKanShape δ c) ≫ rightKanCanonicalShape δ c =
      SSet.yonedaEquiv.symm c :=
  sliceUnderUncurry_fixed _

/-- 元の標準右Kan錐の全射は、同じ形状写像による前合成そのもの。 -/
lemma rightKanCanonicalCone_val {K C D : SSet.{u}} (δ : K ⟶ C) (F : C ⟶ D)
    (c : C _⦋0⦌) : (rightKanCanonicalCone δ F c).val = rightKanCanonicalShape δ c ≫ F := rfl

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
