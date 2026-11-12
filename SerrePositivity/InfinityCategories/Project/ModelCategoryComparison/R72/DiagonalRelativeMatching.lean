module
public import Mathlib.AlgebraicTopology.SimplexCategory.Defs
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.Boundary
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
public import Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex
public import Mathlib.Basic.Opposite
public import Mathlib.Basic.UnivLE
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.CategoryTheory.Comma.Arrow
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.Iso
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Finite
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.WalkingPair
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Cospan
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Iso
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackObjObj
public import Mathlib.CategoryTheory.Limits.Shapes.WidePullbacks
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Types.Basic
public import Mathlib.CategoryTheory.MorphismProperty.Basic
public import Mathlib.CategoryTheory.MorphismProperty.Composition
public import Mathlib.CategoryTheory.NatIso
public import Mathlib.CategoryTheory.NatTrans
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.ObjectProperty.Small
public import Mathlib.CategoryTheory.Opposites
public import Mathlib.CategoryTheory.Products.Basic
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.Combinatorics.Quiver.Basic
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Nat.Basic
public import Mathlib.Logic.Small.Basic
public import Mathlib.Order.Nat
public import Mathlib.Order.RelClasses
public import Mathlib.Order.SuccPred.Nat
public import Mathlib.Tactic.CategoryTheory.Reassoc
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.Index
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.Objects
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.Simplex
public import SerrePositivity.HomotopicalAlgebra.Simplicial.DiagonalInternalHom
public import SerrePositivity.HomotopicalAlgebra.Simplicial.DiagonalRelativeMatching
public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.R72.DiagonalMatching


/-!
分割で生成：docstring を書き直すこと
# 対角の右随伴の相対matching射を実際の境界pullback-Hom射と同型で結ぶ

## 概要
対角の右随伴の相対matching射を実際の境界pullback-Hom射と同型で結ぶ。
一般に再利用できる道具として分類Aに整理する。

## 方針（定義・証明）
境界matching同型とその値方向の自然性を使う。
二つのpullback標的を同型で結び、それらへ入る相対matching射の一致を確認する。

## 規約と注意
宇宙・境界・比較射は各宣言に指定されたものを用いる。
対象ごとの選択から自然性や厳密な合成則を暗黙には推論しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない（依存監査で確認済み）。
今後はWaldhausenのS-構成の二重単体図式や分解の比較・加法性の準備に利用できる。
[棚卸し m0388][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0388
[plan]: ../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Relative matching maps are the actual boundary pullback-Hom maps

The isomorphism compares both pullback targets and the arrows into them.
It uses the proved boundary matching isomorphism and its target naturality.
No model or SM7 assumption is made here.
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open SerrePositivity.Reedy

namespace SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.R72
variable {Z Y : SSet.{v}} (p : Z ⟶ Y) (n : ℕ)

abbrev reedyTargetMap :=
  (matchingEvaluation simplexOp (Opposite.op (SimplexCategory.mk n))).map (_root_.SerrePositivity.BisimplicialModel.internalHomRight.map p)
abbrev reedyRestriction (T : SSet.{v}) (n : ℕ) :=
  (matchingComparison simplexOp (Opposite.op (SimplexCategory.mk n))).app (_root_.SerrePositivity.BisimplicialModel.internalHomRight.obj T)

lemma matchingBoundaryIso_inv_naturality :
    reedyTargetMap p n ≫ (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.R72.matchingBoundaryIso Y n).inv =
      (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.R72.matchingBoundaryIso Z n).inv ≫ _root_.SerrePositivity.BisimplicialModel.boundaryTargetMap p n := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.R72.matchingBoundaryIso_naturality p n
  calc
    _ = (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.R72.matchingBoundaryIso Z n).inv ≫
        ((_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.R72.matchingBoundaryIso Z n).hom ≫ reedyTargetMap p n) ≫
          (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.R72.matchingBoundaryIso Y n).inv := by
      simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
    _ = (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.R72.matchingBoundaryIso Z n).inv ≫
        (_root_.SerrePositivity.BisimplicialModel.boundaryTargetMap p n ≫ (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.R72.matchingBoundaryIso Y n).hom) ≫
          (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.R72.matchingBoundaryIso Y n).inv := by rw [h]
    _ = _ := by simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

lemma matchingBoundaryIso_inv_restriction (T : SSet.{v}) (n : ℕ) :
    reedyRestriction T n ≫ (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.R72.matchingBoundaryIso T n).inv = _root_.SerrePositivity.BisimplicialModel.boundaryRestriction T n := by
  calc
    _ = (_root_.SerrePositivity.BisimplicialModel.boundaryRestriction T n ≫ (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.R72.matchingBoundaryIso T n).hom) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.R72.matchingBoundaryIso T n).inv :=
      congrArg (fun k => k ≫ (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.R72.matchingBoundaryIso T n).inv) (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.R72.matchingBoundaryIso_fac T n).symm
    _ = _ := by simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

abbrev relativeTarget := pullback (reedyRestriction Y n) (reedyTargetMap p n)

abbrev targetMap : pullback (reedyTargetMap p n) (reedyRestriction Y n) ⟶
    (_root_.SerrePositivity.BisimplicialModel.boundaryPullbackHom p n).pt :=
  pullback.map _ _ _ _ (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.R72.matchingBoundaryIso Z n).inv (𝟙 _) (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.R72.matchingBoundaryIso Y n).inv
    (matchingBoundaryIso_inv_naturality p n)
    ((matchingBoundaryIso_inv_restriction Y n).trans (Category.id_comp _).symm)

instance targetMap_isIso : IsIso (targetMap p n) := by
  exact pullback.map_isIso _ _ _ _ _ _ _ _ _

/-- The actual relative matching pullback is the actual boundary pullback-Hom target. -/
def relativeTargetIso : relativeTarget p n ≅ (_root_.SerrePositivity.BisimplicialModel.boundaryPullbackHom p n).pt :=
  pullbackSymmetry _ _ ≪≫ asIso (targetMap p n)

@[reassoc (attr := simp)]
lemma relativeTargetIso_fst : (relativeTargetIso p n).hom ≫ (_root_.SerrePositivity.BisimplicialModel.boundaryPullbackHom p n).fst =
    pullback.snd (reedyRestriction Y n) (reedyTargetMap p n) ≫ (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.R72.matchingBoundaryIso Z n).inv := by
  simp only [relativeTargetIso, Iso.trans_hom, asIso_hom, targetMap, pullback.map,
    _root_.SerrePositivity.BisimplicialModel.boundaryPullbackHom, Functor.PullbackObjObj.ofHasPullback_fst, Category.assoc,
    pullback.lift_fst, pullbackSymmetry_hom_comp_fst_assoc]

@[reassoc (attr := simp)]
lemma relativeTargetIso_snd : (relativeTargetIso p n).hom ≫ (_root_.SerrePositivity.BisimplicialModel.boundaryPullbackHom p n).snd =
    pullback.fst (reedyRestriction Y n) (reedyTargetMap p n) := by
  simp only [relativeTargetIso, Iso.trans_hom, asIso_hom, targetMap, pullback.map,
    _root_.SerrePositivity.BisimplicialModel.boundaryPullbackHom, Functor.PullbackObjObj.ofHasPullback_snd, Category.assoc,
    pullback.lift_snd, Category.comp_id, pullbackSymmetry_hom_comp_snd]

/-- Both source arrows agree under the concrete target isomorphism. -/
lemma relativeTargetIso_fac :
    relativeMatchingMap simplexOp (Opposite.op (SimplexCategory.mk n))
        (_root_.SerrePositivity.BisimplicialModel.internalHomRight.map p) ≫ (relativeTargetIso p n).hom =
      (_root_.SerrePositivity.BisimplicialModel.boundaryPullbackHom p n).π := by
  apply (_root_.SerrePositivity.BisimplicialModel.boundaryPullbackHom p n).hom_ext
  · rw [Category.assoc, relativeTargetIso_fst, ← Category.assoc]
    rw [relativeMatchingMap_snd, Functor.PullbackObjObj.π_fst]
    exact matchingBoundaryIso_inv_restriction Z n
  · rw [Category.assoc, relativeTargetIso_snd]
    rw [relativeMatchingMap_fst, Functor.PullbackObjObj.π_snd]
    rfl

/- 旧宣言の技術注記：
The desired comparison is an isomorphism of actual arrows.
-/
/-- 対角の右随伴の相対matching射を実際の境界pullback-Hom射と同型で結ぶ。

宇宙・境界・比較射は各宣言に指定されたものを用いる。
境界matching同型とその値方向の自然性を使う。
二つのpullback標的を同型で結び、それらへ入る相対matching射の一致を確認する。
-/
def relativeMatchingArrowIso :
    Arrow.mk (relativeMatchingMap simplexOp (Opposite.op (SimplexCategory.mk n))
      (_root_.SerrePositivity.BisimplicialModel.internalHomRight.map p)) ≅ Arrow.mk (_root_.SerrePositivity.BisimplicialModel.boundaryPullbackHom p n).π :=
  Arrow.isoMk (Iso.refl ((ihom (SSet.stdSimplex.{v}.obj (SimplexCategory.mk n))).obj Z))
    (relativeTargetIso p n) (by
      change 𝟙 _ ≫ (_root_.SerrePositivity.BisimplicialModel.boundaryPullbackHom p n).π =
        relativeMatchingMap simplexOp (Opposite.op (SimplexCategory.mk n))
          (_root_.SerrePositivity.BisimplicialModel.internalHomRight.map p) ≫ (relativeTargetIso p n).hom
      exact (Category.id_comp _).trans (relativeTargetIso_fac p n).symm)

end SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.R72
