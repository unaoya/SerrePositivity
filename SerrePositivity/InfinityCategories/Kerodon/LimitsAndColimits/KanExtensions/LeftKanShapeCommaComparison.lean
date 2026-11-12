module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftCommaLift
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.PointSliceHomotopy
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.Shapes

/-!
概要：通常の局所 Kan 添字から cocartesian な置き換えの fiber への比較射を構成する。
方針：slice の標準余錐を区間の指定変換に直し、comma へ持ち上げる。
規約：この段階では比較の同値性は主張しない。
使われ方：点ごとの余極限の添字と置き換えの fiber の図式を比較する。

対応節は Kerodon 7.3（Tag 02Y1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

/-- 概要：局所 Kan 添字の射影に δ を続けると固定頂点へ標準変換がある。
方針：slice の区間表示と pullback の可換条件を使う。
規約：始域と値域は任意の単体集合。
使われ方：oriented fiber product の fiber への持ち上げの入力。 -/
def kanLeftKanShapeHomotopy {K C : SSet.{u}} (δ : K ⟶ C) (c : C _⦋0⦌) :
    SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanProjection δ c ≫ δ) (SSet.const c) where
  h := (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanPointSliceHomotopy c (pullback.snd δ
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm c)))).h
  h₀ := by
    rw [(_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanPointSliceHomotopy c (pullback.snd δ
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm c)))).h₀]
    exact pullback.condition.symm
  h₁ := (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanPointSliceHomotopy c (pullback.snd δ
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm c)))).h₁
  rel := (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanPointSliceHomotopy c (pullback.snd δ
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm c)))).rel

/-- 概要：通常の局所 Kan 添字を置き換えの固定終点の fiber へ写す。
方針：標準の指定変換を comma に持ち上げ、底の定値条件で fiber に制限する。
規約：同値性は後続の比較定理で証明する。
使われ方：局所余極限を cocartesian な射影の fiber の余極限へ移す。 -/
def kanLeftKanShapeToCommaFiber {K C : SSet.{u}} (δ : K ⟶ C) (c : C _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanShape δ c ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaProjection δ) c :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift _ _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaLift δ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanProjection δ c) (SSet.const c) (kanLeftKanShapeHomotopy δ c))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaLift_projection _ _ _ _)

/-- 概要：局所添字の比較は元の K への射影を厳密に保つ。
方針：fiber の包含と comma の持ち上げの射影公式を使う。
規約：δ の単射性などは要求しない。
使われ方：比較の両側で元の図式が同じことを確認する。 -/
lemma kanLeftKanShapeToCommaFiber_source {K C : SSet.{u}} (δ : K ⟶ C) (c : C _⦋0⦌) :
    kanLeftKanShapeToCommaFiber δ c ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaProjection δ) c ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaSource δ = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanProjection δ c := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaLift δ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanProjection δ c) (SSet.const c)
    (kanLeftKanShapeHomotopy δ c) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaSource δ = _
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaLift_source _ _ _ _

/-- 概要：比較射に沿って fiber の図式を制限すると通常の点ごとの Kan 図式となる。
方針：元の添字への射影の一致を図式 F₀ に後合成する。
規約：値域 D の充填性は不要。
使われ方：余極限の比較に必要な図式の厳密な可換性。 -/
lemma kanLeftKanShapeToCommaFiber_diagram {K C D : SSet.{u}}
    (δ : K ⟶ C) (F₀ : K ⟶ D) (c : C _⦋0⦌) :
    kanLeftKanShapeToCommaFiber δ c ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaProjection δ) c ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaSource δ ≫ F₀) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanDiagram δ F₀ c := by
  simpa only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanDiagram] using
    (kanLeftKanShapeToCommaFiber_source δ c =≫ F₀)

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
