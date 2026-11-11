module
public import Mathlib.AlgebraicTopology.Reedy.Basic
public import Mathlib.AlgebraicTopology.SimplexCategory.Defs
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.Boundary
public import Mathlib.AlgebraicTopology.SimplicialSet.Finite
public import Mathlib.AlgebraicTopology.SimplicialSet.Nonsingular
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
public import Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Opposite
public import Mathlib.Basic.UnivLE
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.ConcreteCategory.Basic
public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.Iso
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Finite
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Limits.Preserves.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Types.Basic
public import Mathlib.CategoryTheory.MorphismProperty.Basic
public import Mathlib.CategoryTheory.MorphismProperty.Composition
public import Mathlib.CategoryTheory.NatTrans
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.ObjectProperty.Small
public import Mathlib.CategoryTheory.Opposites
public import Mathlib.CategoryTheory.Products.Basic
public import Mathlib.CategoryTheory.Subfunctor.Basic
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.Combinatorics.Quiver.Basic
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Set.CoeSort
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Data.Subtype
public import Mathlib.Logic.Small.Basic
public import Mathlib.Order.Nat
public import Mathlib.Order.RelClasses
public import Mathlib.Order.SuccPred.Nat
public import Mathlib.Tactic.CategoryTheory.Reassoc
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.BoundaryTensor
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FiniteTensor
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.BoundaryHom
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.Index
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.Objects
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.Simplex
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.SimplexFinite
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.SubcomplexTensor
public import SerrePositivity.HomotopicalAlgebra.Simplicial.DiagonalInternalHom
public import SerrePositivity.HomotopicalAlgebra.Simplicial.DiagonalMatching
public import SerrePositivity.HomotopicalAlgebra.Simplicial.FiniteTensorAdjunction
public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.R72.FiniteTensorAdjunction


/-!
分割で生成：docstring を書き直すこと
# 対角の右随伴のmatching対象を単体境界への内部Homで表す同型を構成する

## 概要
対角の右随伴のmatching対象を単体境界への内部Homで表す同型を構成する。
一般に再利用できる道具として分類Aに整理する。

## 方針（定義・証明）
標準単体のlatching余極限を境界単体と同定する。
反変内部Homが余極限を極限へ移すことを使い、matching比較を境界への制限と照合する。

## 規約と注意
宇宙・境界・比較射は各宣言に指定されたものを用いる。
対象ごとの選択から自然性や厳密な合成則を暗黙には推論しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない（依存監査で確認済み）。
今後はWaldhausenのS-構成の二重単体図式や分解の比較・加法性の準備に利用できる。
[棚卸し m0386][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0386
[plan]: ../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Matching objects of the concrete diagonal right adjoint

The actual latching colimit of standard simplices is the boundary simplex.
Contravariant internal Hom turns this colimit into the actual matching
limit. The comparison formula identifies restriction along the boundary.
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open SerrePositivity.Reedy SerrePositivity.HomotopyFunctionComplex

namespace SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.R72

/-- The actual latching object of standard simplices is the standard boundary. -/
def standardBoundaryIso (n : ℕ) :
    (latchingEvaluation simplex (SimplexCategory.mk n)).obj SSet.stdSimplex.{v} ≅
      (SSet.boundary.{v} n).toSSet :=
  (boundaryTensorIso SSet.stdSimplex.{v} n).symm ≪≫
    _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.R72.tensorIso (𝟭 SSet.{v}) (SSet.boundary n).toSSet

@[reassoc]
lemma standardBoundaryIso_fac (n : ℕ) :
    (standardBoundaryIso.{v} n).hom ≫ (SSet.boundary n).ι =
      (latchingComparison simplex (SimplexCategory.mk n)).app SSet.stdSimplex.{v} := by
  change (boundaryTensorIso SSet.stdSimplex.{v} n).inv ≫
      (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.R72.tensorIso (𝟭 SSet.{v}) (SSet.boundary n).toSSet).hom ≫
        (𝟭 SSet.{v}).map (SSet.boundary n).ι = _
  rw [_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.R72.tensorIso_inclusion, boundaryTensorIso_comparison]
  exact Iso.inv_hom_id_assoc _ _

/-- 対角の右随伴のmatching対象を単体境界への内部Homで表す同型を構成する。

宇宙・境界・比較射は各宣言に指定されたものを用いる。
標準単体のlatching余極限を境界単体と同定する。
反変内部Homが余極限を極限へ移すことを使い、matching比較を境界への制限と照合する。
-/
def matchingBoundaryIso (Z : SSet.{v}) (n : ℕ) :
    (ihom (SSet.boundary.{v} n).toSSet).obj Z ≅
      (matchingEvaluation simplexOp (Opposite.op (SimplexCategory.mk n))).obj
        (_root_.SerrePositivity.BisimplicialModel.internalHomRight.obj Z) :=
  (_root_.SerrePositivity.BisimplicialModel.boundaryHom Z).mapIso (standardBoundaryIso n).op ≪≫
    BoundaryHom.iso simplex (SimplexCategory.mk n) SSet.stdSimplex.{v} (_root_.SerrePositivity.BisimplicialModel.boundaryHom Z)

/-- The matching map is exactly restriction from the standard simplex to its boundary. -/
@[reassoc]
lemma matchingBoundaryIso_fac (Z : SSet.{v}) (n : ℕ) :
    (MonoidalClosed.internalHom.map (SSet.boundary.{v} n).ι.op).app Z ≫
      (matchingBoundaryIso Z n).hom =
        (matchingComparison simplexOp (Opposite.op (SimplexCategory.mk n))).app
          (_root_.SerrePositivity.BisimplicialModel.internalHomRight.obj Z) := by
  change (_root_.SerrePositivity.BisimplicialModel.boundaryHom Z).map (SSet.boundary n).ι.op ≫
      ((_root_.SerrePositivity.BisimplicialModel.boundaryHom Z).map (standardBoundaryIso n).hom.op ≫
        (BoundaryHom.iso simplex (SimplexCategory.mk n) SSet.stdSimplex.{v}
          (_root_.SerrePositivity.BisimplicialModel.boundaryHom Z)).hom) = _
  rw [← Category.assoc, ← (_root_.SerrePositivity.BisimplicialModel.boundaryHom Z).map_comp, ← op_comp, standardBoundaryIso_fac]
  exact BoundaryHom.comparison simplex (SimplexCategory.mk n) SSet.stdSimplex.{v} (_root_.SerrePositivity.BisimplicialModel.boundaryHom Z)

/-- Naturality of the actual boundary matching isomorphism in the target. -/
@[reassoc]
lemma matchingBoundaryIso_naturality {Z Z' : SSet.{v}} (p : Z ⟶ Z') (n : ℕ) :
    (matchingBoundaryIso Z n).hom ≫
        (matchingEvaluation simplexOp (Opposite.op (SimplexCategory.mk n))).map
          (_root_.SerrePositivity.BisimplicialModel.internalHomRight.map p) =
      (ihom (SSet.boundary n).toSSet).map p ≫ (matchingBoundaryIso Z' n).hom := by
  let t := MonoidalClosed.internalHom.flip.map p
  let e := standardBoundaryIso.{v} n
  let i := BoundaryHom.iso simplex (SimplexCategory.mk n) SSet.stdSimplex.{v} (_root_.SerrePositivity.BisimplicialModel.boundaryHom Z)
  let i' := BoundaryHom.iso simplex (SimplexCategory.mk n) SSet.stdSimplex.{v} (_root_.SerrePositivity.BisimplicialModel.boundaryHom Z')
  have hnat := BoundaryHom.iso_naturality simplex (SimplexCategory.mk n)
    SSet.stdSimplex.{v} (_root_.SerrePositivity.BisimplicialModel.boundaryHom Z) t
  have he := t.naturality e.hom.op
  change ((_root_.SerrePositivity.BisimplicialModel.boundaryHom Z).map e.hom.op ≫ i.hom) ≫ _ =
    t.app (Opposite.op (SSet.boundary n).toSSet) ≫ ((_root_.SerrePositivity.BisimplicialModel.boundaryHom Z').map e.hom.op ≫ i'.hom)
  rw [Category.assoc]
  refine (congrArg (fun k => (_root_.SerrePositivity.BisimplicialModel.boundaryHom Z).map e.hom.op ≫ k) hnat).trans ?_
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ i'.hom) he).trans (Category.assoc _ _ _))

end SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.R72
