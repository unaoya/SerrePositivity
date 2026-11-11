module
public import Mathlib.AlgebraicTopology.SimplexCategory.Defs
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Opposite
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Adjunction.Parametrized
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.CategoryTheory.ConcreteCategory.Basic
public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.Iso
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Monoidal.Category
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Types.Basic
public import Mathlib.CategoryTheory.NatIso
public import Mathlib.CategoryTheory.NatTrans
public import Mathlib.CategoryTheory.Opposites
public import Mathlib.CategoryTheory.Products.Basic
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.Combinatorics.Quiver.Basic
public import Mathlib.Logic.Equiv.Defs
public import SerrePositivity.HomotopicalAlgebra.Simplicial.DiagonalRepresentables
public import SerrePositivity.HomotopicalAlgebra.Simplicial.StandardSimplexCosimplicialHom
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.AdjunctionHom


/-!
# 対角の右随伴を標準単体の内部Homで表す随伴を構成する

## 概要
対角の右随伴を標準単体の内部Homで表す随伴を構成する。
一般に再利用できる道具として分類Aに整理する。

## 方針（定義・証明）
制限された表現可能関手の計算に閉構造の随伴を適用する。
標準単体のYoneda同型と合わせ、行と値の両変数で自然性を確認する。

## 規約と注意
宇宙・境界・比較射は各宣言に指定されたものを用いる。
対象ごとの選択から自然性や厳密な合成則を暗黙には推論しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない（依存監査で確認済み）。
今後はWaldhausenのS-構成の二重単体図式や分解の比較・加法性の準備に利用できる。
[棚卸し m0383][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0383
[plan]: ../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Rows of the actual diagonal right adjoint are internal Homs

The representable computation, the closed adjunction, and the actual
standard-simplex Yoneda isomorphism identify each row naturally in both
its simplicial operators and the target. No model hypotheses are used.
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.MonoidalCategory
open SerrePositivity.HomotopyFunctionComplex

namespace SerrePositivity.BisimplicialModel

abbrev tensorFrame (n : SimplexCategory) : SimplexCategory ⥤ SSet.{v} :=
  SSet.stdSimplex ⋙ tensorLeft (SSet.stdSimplex.obj n)

/-- Identify an entire row, with both inner-simplex and target naturality. -/
def rightAdjointRowTensorIso (n : SimplexCategory) :
    rightAdjoint.{v} ⋙ (CategoryTheory.evaluation SimplexCategoryᵒᵖ SSet.{v}).obj
      (Opposite.op n) ≅ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom (tensorFrame n) :=
  NatIso.ofComponents (fun Z => NatIso.ofComponents
    (fun m => Equiv.toIso (rightAdjointValueEquiv Z n m.unop)) (by
      intro m l g
      ext x
      exact rightAdjointValueEquiv_inner Z n g.unop x)) (by
    intro Z Z' h
    ext m x
    exact rightAdjointValueEquiv_target h n m.unop x)

/-- The actual right Kan extension row is the actual closed internal Hom. -/
def rightAdjointRowInternalHomIso (n : SimplexCategory) :
    rightAdjoint.{v} ⋙ (CategoryTheory.evaluation SimplexCategoryᵒᵖ SSet.{v}).obj
      (Opposite.op n) ≅ ihom (SSet.stdSimplex.obj n) :=
  rightAdjointRowTensorIso n ≪≫
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.adjunctionHomIsoSameUniverse (ihom.adjunction (SSet.stdSimplex.obj n)) SSet.stdSimplex ≪≫
    Functor.isoWhiskerLeft _ QuillenStandardFrame.homIso ≪≫ Functor.rightUnitor _

@[simp]
lemma rightAdjointRowInternalHomIso_formula (Z : SSet.{v}) (n m : SimplexCategory)
    (x : ((rightAdjoint.obj Z).obj (Opposite.op n)).obj (Opposite.op m)) :
    ((rightAdjointRowInternalHomIso n).hom.app Z).app (Opposite.op m) x =
      SSet.yonedaEquiv ((ihom.adjunction (SSet.stdSimplex.obj n)).homEquiv
        (SSet.stdSimplex.obj m) Z (rightAdjointValueEquiv Z n m x)) := rfl

lemma rightAdjointRowInternalHomIso_outer (Z : SSet.{v}) {n' n : SimplexCategory}
    (g : n' ⟶ n) :
    (rightAdjoint.obj Z).map g.op ≫ (rightAdjointRowInternalHomIso n').hom.app Z =
      (rightAdjointRowInternalHomIso n).hom.app Z ≫
        (MonoidalClosed.internalHom.map (SSet.stdSimplex.map g).op).app Z := by
  ext m x
  let adj := MonoidalClosed.internalHomAdjunction₂ (C := SSet.{v})
  let h := rightAdjointValueEquiv Z n m.unop x
  let p := (MonoidalClosed.internalHom.map (SSet.stdSimplex.map g).op).app Z
  change ((rightAdjointRowInternalHomIso n').hom.app Z).app m
      (((rightAdjoint.obj Z).map g.op).app m x) =
    p.app m (((rightAdjointRowInternalHomIso n).hom.app Z).app m x)
  calc
    _ = SSet.yonedaEquiv ((ihom.adjunction (SSet.stdSimplex.obj n')).homEquiv
        (SSet.stdSimplex.obj m.unop) Z
          (rightAdjointValueEquiv Z n' m.unop (((rightAdjoint.obj Z).map g.op).app m x))) :=
      rightAdjointRowInternalHomIso_formula _ _ _ _
    _ = SSet.yonedaEquiv ((ihom.adjunction (SSet.stdSimplex.obj n')).homEquiv
        (SSet.stdSimplex.obj m.unop) Z
          ((SSet.stdSimplex.map g ▷ SSet.stdSimplex.obj m.unop) ≫ h)) :=
      congrArg (fun k => SSet.yonedaEquiv ((ihom.adjunction (SSet.stdSimplex.obj n')).homEquiv
        (SSet.stdSimplex.obj m.unop) Z k)) (rightAdjointValueEquiv_outer Z g m.unop x)
    _ = SSet.yonedaEquiv (adj.homEquiv h ≫ p) :=
      congrArg SSet.yonedaEquiv (adj.homEquiv_naturality_one (SSet.stdSimplex.map g) h)
    _ = p.app m (SSet.yonedaEquiv (adj.homEquiv h)) := SSet.yonedaEquiv_comp _ _
    _ = _ := congrArg (fun k => p.app m k)
      (rightAdjointRowInternalHomIso_formula Z n m.unop x).symm

/-- The explicit internal-Hom family, in all outer degrees. -/
abbrev internalHomRight : SSet.{v} ⥤ SimplexCategoryᵒᵖ ⥤ SSet.{v} :=
  (SSet.stdSimplex.op ⋙ MonoidalClosed.internalHom).flip

/- 旧宣言の技術注記：
The actual right Kan extension is naturally the standard-simplex internal Hom.
-/
/-- 対角の右随伴を各行の内部Homで表す自然同型を構成する。

宇宙・境界・比較射は各宣言に指定されたものを用いる。
制限された表現可能関手の計算に閉構造の随伴を適用する。
標準単体のYoneda同型と合わせ、行と値の両変数で自然性を確認する。
-/
def rightAdjointInternalHomIso : rightAdjoint.{v} ≅ internalHomRight.{v} :=
  NatIso.ofComponents (fun Z => NatIso.ofComponents
    (fun n => (rightAdjointRowInternalHomIso n.unop).app Z) (by
      intro n m g
      exact rightAdjointRowInternalHomIso_outer Z g.unop)) (by
    intro Z Z' h
    apply NatTrans.ext
    funext n
    exact (rightAdjointRowInternalHomIso n.unop).hom.naturality h)

/- 旧宣言の技術注記：
The diagonal adjunction with the now explicit internal-Hom right adjoint.
-/
/-- 対角の右随伴を標準単体の内部Homで表す随伴を構成する。

宇宙・境界・比較射は各宣言に指定されたものを用いる。
制限された表現可能関手の計算に閉構造の随伴を適用する。
標準単体のYoneda同型と合わせ、行と値の両変数で自然性を確認する。
-/
def diagonalInternalHomAdjunction : diagonal.{v} ⊣ internalHomRight.{v} :=
  diagonalAdjunction.ofNatIsoRight rightAdjointInternalHomIso

instance internalHomRight_isRightAdjoint : internalHomRight.{v}.IsRightAdjoint :=
  diagonalInternalHomAdjunction.isRightAdjoint

end SerrePositivity.BisimplicialModel
