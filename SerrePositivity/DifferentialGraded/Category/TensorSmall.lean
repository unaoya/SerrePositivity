module
public import SerrePositivity.DifferentialGraded.Category.Tensor

/-! # 小さい二つのdg圏のtensor積の対象のsmall性

## 概要
小さい二つのdg圏のtensor積の対象のsmall性。

## 方針
既存の全dg自然なHom・作用・chain mapと局所化の計算を再利用する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanの依存。直接の利用箇所：Bimodule/TensorModuleMaps.lean。dg加群の導来作用・準同値比較の基盤。
任意可換環上のMorita・K理論のモデル比較に再利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/
@[expose] public section
universe u v w
namespace SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w)
  [DGCategory A B] [DGCategory A C] [Small.{u} B] [Small.{u} C]

instance dgTensorSmall : Small.{u} (DGTensorCategory A B C) :=
  inferInstanceAs (Small.{u} (B × C))

end SerrePositivity.DifferentialGraded
