module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.ElementsChainLifting
public import SerrePositivity.HomotopicalAlgebra.Simplicial.BarConstruction
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic

/-!
# bar の転置した行の余積表示

## 概要
元の bar の行を転置すると、基底の射列を添字とする値の余積になる。

## 方針（定義・証明）
要素圏の射列を基底の射列と最初のラベルから復元し、余積の普遍性を示す。

## 規約と注意
添字と値の宇宙を分ける。単体集合のモデル構造は仮定しない。

## 使われ方
固定右脚の Hom の不変性を bar 全体の不変性に移すために使う。
-/

@[expose] public section
universe v uD vD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits

namespace SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.BarRows
open _root_.SerrePositivity.SimplicialModel

variable {D : Type uD} [Category.{vD} D] (F : D ⥤ SSet.{v})

/-- 元の二重単体的 bar の二方向を交換した行。 -/
abbrev row (n : SimplexCategoryᵒᵖ) : SSet.{max uD vD v} :=
  ((BarConstruction.rows D).obj F).flip.obj n

/-- 同じ基底射列の最初の値を、要素圏の実際の射列に送る。 -/
def inclusion (n : SimplexCategoryᵒᵖ) (c : ComposableArrows D n.unop.len) :
    SSet.uliftFunctor.{max uD vD, v}.obj (F.obj (c.obj 0)) ⟶ _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.BarRows.row F n where
  app m := ↾fun x => _root_.SerrePositivity.LabelledChain.lift (F.flip.obj m) c x.down
  naturality {m m'} θ := by
    ext x
    exact (_root_.SerrePositivity.LabelledChain.map (F.flip.obj m) c x.down (F.flip.map θ)).symm

/-- 全基底射列からの包含を持つ、元の転置した行上の余錐。 -/
def cofan (n : SimplexCategoryᵒᵖ) :
    Cofan (fun c : ComposableArrows D n.unop.len =>
      SSet.uliftFunctor.{max uD vD, v}.obj (F.obj (c.obj 0))) :=
  Cofan.mk (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.BarRows.row F n) (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.BarRows.inclusion F n)

/-- 最初のラベルによる復元で、指定された包含から余錐へ降下する。 -/
def desc (n : SimplexCategoryᵒᵖ)
    (s : Cofan (fun c : ComposableArrows D n.unop.len =>
      SSet.uliftFunctor.{max uD vD, v}.obj (F.obj (c.obj 0)))) : _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.BarRows.row F n ⟶ s.pt where
  app m := ↾fun e => (s.inj (e ⋙ Functor.Elements.π (F.flip.obj m))).app m
    ⟨(e.obj 0).val⟩
  naturality {m m'} θ := by
    ext e
    exact ConcreteCategory.congr_hom ((s.inj (e ⋙ Functor.Elements.π (F.flip.obj m))).naturality θ)
      ⟨(e.obj 0).val⟩

/-- 転置した各行は、値の宇宙を拡大した実際の余積である。 -/
def isColimit (n : SimplexCategoryᵒᵖ) : IsColimit (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.BarRows.cofan F n) := by
  refine Cofan.IsColimit.mk _ (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.BarRows.desc F n) ?_ ?_
  · intro s c
    ext m x
    change (s.inj c).app m
      ⟨(F.flip.obj m).map (c.map (homOfLE (Fin.zero_le 0))) x.down⟩ = _
    rw [show homOfLE (Fin.zero_le (0 : Fin (n.unop.len + 1))) = 𝟙 0 from
      Subsingleton.elim _ _, c.map_id, CategoryTheory.Functor.map_id]
    cases x
    rfl
  · intro s k hk
    ext m e
    have h := ConcreteCategory.congr_hom (congr_app (hk (e ⋙ Functor.Elements.π (F.flip.obj m))) m)
      (⟨(e.obj 0).val⟩ : ULift.{max uD vD} ((F.flip.obj m).obj (e.obj 0).obj))
    change k.app m (_root_.SerrePositivity.LabelledChain.lift (F.flip.obj m)
      (e ⋙ Functor.Elements.π (F.flip.obj m)) (e.obj 0).val) = _ at h
    change k.app m e = _
    exact (congrArg (fun t => k.app m t) (_root_.SerrePositivity.LabelledChain.reconstruct (F.flip.obj m) e)).symm.trans h

end SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.BarRows
