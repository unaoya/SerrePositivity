module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.CommutativeAlgebra
public import Mathlib.CategoryTheory.Monoidal.CommMon_

/-!
模型。文献の定義との比較は後で
# 可換モノイド複体から Com 代数への関手

概要：BM §1 の Com 代数化を射と合成も含めて束ねる。
方針：モノイド射の全入力の作用保存を使う。
規約：底の複体と射を厳密に保持する。
使われ方：離散可換代数から E 代数への関手の中間段階。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads

open _root_.CategoryTheory
open _root_.SerrePositivity.DifferentialGraded

variable (A : Type u) [CommRing A]

/-- 概要：可換モノイド複体を全入力の Com 代数へ送る関手（BM §1）。
方針：反復積による対象と、同じ底のモノイド射を用いる。
規約：底の複体と射は変えない。
使われ方：離散可換代数の Com 代数化。 -/
def commutativeAlgebraFunctor : CommMon (Complex A) ⥤ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.commutativeOperad A).Algebra where
  obj X := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.commutativeAlgebraOfMonoid X.X
  map f := by
    have : IsMonHom f.hom.hom := f.hom.isMonHom_hom
    exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.commutativeAlgebraMap f.hom.hom
  map_id X := by apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.AlgebraHom.ext; rfl
  map_comp f g := by apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.AlgebraHom.ext; rfl

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
