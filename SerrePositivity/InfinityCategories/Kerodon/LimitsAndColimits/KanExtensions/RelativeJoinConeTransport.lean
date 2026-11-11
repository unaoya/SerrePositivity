module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeJoinRightShiftPrism
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.ComparisonCocartesian

/-!
概要：相対 join の局所錐を右指定自然変換の比較錐として表示する。
方針：右移動 prism を図式で写し、四境界を輸送のフィールドへ渡す。
規約：輸送の存在を追加仮定せず、実際の族を構成する。
使われ方：相対 join 上の右 Kan 条件と局所極限性の比較。

対応節は Kerodon 7.3（Tag 02Y1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

/-- 概要：右 relative join 上の図式の標準 prism による指定自然変換。
方針：標準右 prism に図式を後合成し、両端の式を使う。
規約：変換の向きは左端の δ に沿う制限から右端。
使われ方：右局所比較錐の指定変換。 -/
def kanRelativeJoinRightTransformation {K C D : SSet.{u}} (δ : K ⟶ C)
    (G : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin (𝟙 C) δ ⟶ D) :
    SSet.Homotopy (δ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInl (𝟙 C) δ ≫ G) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInr (𝟙 C) δ ≫ G) where
  h := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinRightPrism δ ≫ G
  h₀ := by
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinRightPrism_zero, Category.assoc]
    rfl
  h₁ := by
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinRightPrism_one]
    rfl
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

/-- 概要：相対 join の局所錐から指定変換に両立する実際の右輸送を構成する。
方針：coslice の普遍錐の右移動 prism に G を後合成し、四境界を使う。
規約：D の quasicategory 性を構成には要求しない。
使われ方：局所錐の極限性を右 Kan 条件へ移す。 -/
def kanRelativeJoinConeTransport {K C D : SSet.{u}} (δ : K ⟶ C)
    (G : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin (𝟙 C) δ ⟶ D) (c : C _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RightKanConeTransport δ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInr (𝟙 C) δ ≫ G)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInl (𝟙 C) δ ≫ G) (kanRelativeJoinRightTransformation δ G) c where
  family := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinRightShiftPrism δ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanProjection δ c)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry (pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm c)) δ))
    (by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.sliceUnderUncurry_projection, pullback.condition]) ≫ G
  start := by
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinRightShiftPrism_zero]
    rfl
  diagram := by
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinRightShiftPrism_right]
    rfl
  fixedVertex := by
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinRightShiftPrism_left]
    rfl

/-- 概要：右輸送の比較錐は元の相対 join の局所錐と同じ射を持つ。
方針：右移動 prism の終点を計算し、coslice の固定端の式を使う。
規約：raw な射の等式。
使われ方：両表示の極限性の比較。 -/
lemma kanRelativeJoinConeTransport_cone_val {K C D : SSet.{u}} (δ : K ⟶ C)
    (G : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin (𝟙 C) δ ⟶ D) (c : C _⦋0⦌) :
    (kanRelativeJoinConeTransport δ G c).cone.val =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinDiagramCone δ c G).val := by
  change SSet.ι₁ ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinRightShiftPrism δ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanProjection δ c)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry (pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm c)) δ)) _ ≫ G) = _
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinRightShiftPrism_one]
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_fixed]
  rfl

/-- 概要：構成した右比較錐は相対 join の局所錐に等しい。
方針：raw な射の等式から部分型の外延性を使う。
規約：同じ制限図式上の錐として比較する。
使われ方：右 Kan 条件と局所極限性の同値。 -/
lemma kanRelativeJoinConeTransport_cone {K C D : SSet.{u}} (δ : K ⟶ C)
    (G : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin (𝟙 C) δ ⟶ D) (c : C _⦋0⦌) :
    (kanRelativeJoinConeTransport δ G c).cone = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinDiagramCone δ c G :=
  Subtype.ext (kanRelativeJoinConeTransport_cone_val δ G c)

/-- 概要：標準右指定変換の右 Kan 条件は相対 join の局所錐の極限性と同値。
方針：実際の局所輸送と比較錐の選択不変性を合わせる。
規約：D の quasicategory 性を使うが δ の単射性は不要。
使われ方：点ごとの右 Kan 条件を相対 join の図式の制限として扱う。 -/
lemma isRightKanExtension_relativeJoin_iff_local_limits {K C D : SSet.{u}}
    [Quasicategory D] (δ : K ⟶ C) (G : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin (𝟙 C) δ ⟶ D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsRightKanExtension δ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInr (𝟙 C) δ ≫ G) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInl (𝟙 C) δ ≫ G)
      (kanRelativeJoinRightTransformation δ G) ↔
      ∀ c : C _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinDiagramCone δ c G) := by
  constructor
  · intro h c
    have ht := (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.isRightKanExtension_iff_forall_transport δ _ _ _).1 h c
      (kanRelativeJoinConeTransport δ G c)
    rwa [kanRelativeJoinConeTransport_cone] at ht
  · intro h c
    refine ⟨kanRelativeJoinConeTransport δ G c, ?_⟩
    rw [kanRelativeJoinConeTransport_cone]
    exact h c

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
