module
public import SerrePositivity.DifferentialGraded.Category.Tensor
public import SerrePositivity.DifferentialGraded.Functor.Basic

/-! # 二つのdg関手のtensor積

## 概要
Hom chain mapのtensor積と、Mathlib tensorμの自然性を使う。

## 方針
既存の全dg自然なHom・作用・chain mapと局所化の計算を再利用する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。dg加群の導来作用・準同値比較の基盤。任意可換環上のMorita・K理論のモデル比較に再利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z t
namespace SerrePositivity.DifferentialGraded.DGFunctor
open CategoryTheory MonoidalCategory
variable {A : Type u} [CommRing A] {B : Type v} {C : Type w} {D : Type z} {E : Type t}
  [DGCategory A B] [DGCategory A C] [DGCategory A D] [DGCategory A E]

def tensor (F : DGFunctor A B D) (G : DGFunctor A C E) :
    DGFunctor A (DGTensorCategory A B C) (DGTensorCategory A D E) where
  obj x := (F.obj x.1, G.obj x.2)
  map x y := F.map x.1 y.1 ⊗ₘ G.map x.2 y.2
  map_id x := by
    rw [dgTensor_identity, dgTensor_identity, Category.assoc,
      tensorHom_comp_tensorHom, F.map_id, G.map_id]
  map_comp x y z := by
    rw [dgTensor_composition, dgTensor_composition, Category.assoc,
      tensorHom_comp_tensorHom, F.map_comp, G.map_comp,
      ← tensorHom_comp_tensorHom, ← Category.assoc, ← tensorμ_natural, Category.assoc]

end SerrePositivity.DifferentialGraded.DGFunctor
