module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.CommutativeAlgebraFunctor
public import SerrePositivity.HomologicalAlgebra.CochainDiscreteAlgebra
public import Mathlib.Algebra.Category.CommAlgCat.Basic

/-!
模型。文献の定義との比較は後で
# 離散可換代数の Com 代数構造

概要：BM §1 の Com 代数を、任意の通常の可換代数の零次複体上に構成する。
方針：通常の積を可換モノイド加群にし、既存の対称モノイダル零次埋め込みを使う。
規約：任意の可換基礎環、元の積・単位と底の加群を使う。
使われ方：E2a-4 の離散可換代数の E 代数化と E2b の離散対象。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory

variable (A : Type u) [CommRing A]

/-- 概要：通常の可換 A 代数を可換モノイド加群とする（BM §1）。
方針：既存の積と代数写像のモノイド構造に、積の可換性を加える。
規約：底は元の A 加群。
使われ方：対称モノイダル零次埋め込みの入力。 -/
def moduleCommMonoid (B : Type u) [CommRing B] [Algebra A B] : CommMon (ModuleCat A) := by
  let := SerrePositivity.moduleAlgebraMonObj (R := A) B
  have : IsCommMonObj (ModuleCat.of A B) := by
    refine { mul_comm := ?_ }
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    exact mul_comm y x
  exact { X := ModuleCat.of A B }

/-- 概要：通常の可換代数射は可換モノイド加群の射（BM §1）。
方針：単位と二項積の保存を元ごとに検証する。
規約：底の射は元の A 線形写像。
使われ方：離散代数の関手の射成分。 -/
def moduleCommMonoidMap {B D : Type u} [CommRing B] [CommRing D]
    [Algebra A B] [Algebra A D] (f : B →ₐ[A] D) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.moduleCommMonoid A B ⟶ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.moduleCommMonoid A D :=
  CommMon.homMk {
    hom := ModuleCat.ofHom f.toLinearMap
    isMonHom_hom := {
      one_hom := by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro a
        exact f.commutes a
      mul_hom := by
        apply ModuleCat.hom_ext
        apply TensorProduct.ext
        apply LinearMap.ext
        intro x
        apply LinearMap.ext
        intro y
        exact f.map_mul x y } }

/-- 概要：通常の可換代数から可換モノイド加群への関手（BM §1）。
方針：元の加群・単位・積と同じ線形写像を使う。
規約：基礎環と代数の宇宙は u。
使われ方：零次複体上の Com 代数化の前段。 -/
def moduleCommMonoidFunctor : CommAlgCat.{u} A ⥤ CommMon (ModuleCat A) where
  obj B := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.moduleCommMonoid A B
  map f := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.moduleCommMonoidMap A f.hom
  map_id B := by apply CommMon.hom_ext; rfl
  map_comp f g := by apply CommMon.hom_ext; rfl

/-- 概要：離散可換代数の零次複体上の全入力 Com 代数（BM §1）。
方針：可換モノイド加群を対称モノイダル零次埋め込みで移し、反復積を作用にする。
規約：零入力は元の単位、全ての整数次数を持つ複体として扱う。
使われ方：E → Com に沿う制限の入力と E2b の離散対象。 -/
def discreteCommutativeFunctor : CommAlgCat.{u} A ⥤ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.commutativeOperad A).Algebra :=
  _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.moduleCommMonoidFunctor A ⋙
    (CochainComplex.singleFunctor (ModuleCat A) 0).mapCommMon ⋙ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.commutativeAlgebraFunctor A

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
