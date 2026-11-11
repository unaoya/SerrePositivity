module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoreLimit
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.Cocone
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：左右 Kan 拡張の点ごとの添字と、その上の標準の錐・余錐。
方針：coslice・slice 射影への通常の引き戻しと、普遍錐の uncurry を使う。
規約：右は C_{c/} ×_C K、左は K ×_C C_{/c}。単なる頂点の集合へ置き換えない。
使われ方：Kerodon Notation 7.3.1.1（Tag 02Y8）、Def 7.3.1.2（Tag 02Y9）、Variant 7.3.1.5（Tag 02YC）。

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

/-- 概要：右 Kan 拡張の頂点 c での coslice 引き戻し。
方針：coslice の終点射影に δ を引き戻す。
規約：因子の順序は原典の C_{c/} ×_C K。
使われ方：右 Kan 拡張の極限公式。 -/
abbrev rightKanShape {K C : SSet.{u}} (δ : K ⟶ C) (c : C _⦋0⦌) : SSet.{u} :=
  pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm c)) δ

/-- 概要：左 Kan 拡張の頂点 c での slice 引き戻し。
方針：δ に slice の始点射影を引き戻す。
規約：因子の順序は原典の K ×_C C_{/c}。
使われ方：左 Kan 拡張の余極限公式。 -/
abbrev leftKanShape {K C : SSet.{u}} (δ : K ⟶ C) (c : C _⦋0⦌) : SSet.{u} :=
  pullback δ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm c))

/-- 概要：右 Kan 拡張の点ごとの図式の K への射影。
方針：引き戻しの第二射影。
規約：coslice の射影への射ではない。
使われ方：元の図式 F₀ の制限。 -/
abbrev rightKanProjection {K C : SSet.{u}} (δ : K ⟶ C) (c : C _⦋0⦌) :
    rightKanShape δ c ⟶ K := pullback.snd _ _

/-- 概要：左 Kan 拡張の点ごとの図式の K への射影。
方針：引き戻しの第一射影。
規約：slice の射影への射ではない。
使われ方：元の図式 F₀ の制限。 -/
abbrev leftKanProjection {K C : SSet.{u}} (δ : K ⟶ C) (c : C _⦋0⦌) :
    leftKanShape δ c ⟶ K := pullback.fst _ _

/-- 概要：右 Kan 拡張の頂点 c で極限を取る図式。
方針：K への射影と元の図式を合成する。
規約：値域 D の充填性は定義に不要。
使われ方：Kerodon Def 7.3.1.2（Tag 02Y9） の点ごとの極限。 -/
@[kerodon 02Y9]
def rightKanDiagram {K C D : SSet.{u}} (δ : K ⟶ C) (F₀ : K ⟶ D) (c : C _⦋0⦌) :
    rightKanShape δ c ⟶ D := rightKanProjection δ c ≫ F₀

/-- 概要：左 Kan 拡張の頂点 c で余極限を取る図式。
方針：K への射影と元の図式を合成する。
規約：値域 D の充填性は定義に不要。
使われ方：Kerodon Variant 7.3.1.5（Tag 02YC） の点ごとの余極限。 -/
@[kerodon 02YC]
def leftKanDiagram {K C D : SSet.{u}} (δ : K ⟶ C) (F₀ : K ⟶ D) (c : C _⦋0⦌) :
    leftKanShape δ c ⟶ D := leftKanProjection δ c ≫ F₀

/-- 概要：coslice の普遍錐に関手 F を適用した標準の錐。
方針：coslice への引き戻し射影を uncurry して F を合成する。
規約：ここでの図式は δ≫F。指定自然変換による輸送は後で行う。
使われ方：右 Kan 拡張の比較錐の始点。 -/
def rightKanCanonicalCone {K C D : SSet.{u}} (δ : K ⟶ C) (F : C ⟶ D) (c : C _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (rightKanDiagram δ (δ ≫ F) c) :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry (pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm c)) δ) ≫ F, by
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.sliceUnderUncurry_projection, pullback.condition]
    rfl⟩

/-- 概要：標準の右比較錐の頂点は F(c)。
方針：左の固定因子への制限を Yoneda 対応で読む。
規約：頂点は厳密に同じ零単体。
使われ方：右 Kan 拡張の極限対象の値の同定。 -/
lemma rightKanCanonicalCone_vertex {K C D : SSet.{u}} (δ : K ⟶ C) (F : C ⟶ D)
    (c : C _⦋0⦌) : (rightKanCanonicalCone δ F c).vertex = F.app _ c := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone.vertex_eq]
  change SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl _ _ ≫ (_ ≫ F)) = _
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_fixed, SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]

/-- 概要：slice の普遍余錐に関手 F を適用した標準の余錐。
方針：slice への引き戻し射影を uncurry して F を合成する。
規約：ここでの図式は δ≫F。指定自然変換による輸送は後で行う。
使われ方：左 Kan 拡張の比較余錐の終端。 -/
def leftKanCanonicalCocone {K C D : SSet.{u}} (δ : K ⟶ C) (F : C ⟶ D) (c : C _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (leftKanDiagram δ (δ ≫ F) c) :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry (pullback.snd δ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm c))) ≫ F, by
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.sliceOverUncurry_projection, ← pullback.condition]
    rfl⟩

/-- 概要：標準の左比較余錐の頂点は F(c)。
方針：右の固定因子への制限を Yoneda 対応で読む。
規約：頂点は厳密に同じ零単体。
使われ方：左 Kan 拡張の余極限対象の値の同定。 -/
lemma leftKanCanonicalCocone_vertex {K C D : SSet.{u}} (δ : K ⟶ C) (F : C ⟶ D)
    (c : C _⦋0⦌) : (leftKanCanonicalCocone δ F c).vertex = F.app _ c := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.vertex_eq]
  change SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr _ _ ≫ (_ ≫ F)) = _
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry_fixed, SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
