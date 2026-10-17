module
public import SerrePositivity.DifferentialGraded.Module.LeftQuasiIso

/-! # 左右加群同値の逆関手による指定準同型クラスの保存・反映

## 概要
左右加群同値の逆関手による指定準同型クラスの保存・反映。

## 方針
既存の全dg自然なHom・作用・chain mapと局所化の計算を再利用する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanの依存。直接の利用箇所：Tensor/LeftKFlatResolution.lean。dg加群の導来作用・準同値比較の基盤。
任意可換環上のMorita・K理論のモデル比較に再利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma leftRightOpposite_inverse_quasiIso_iff {M N : ModuleCategory A Dᵒᵖ} (f : M ⟶ N) :
    leftModuleQuasiIso A D ((leftRightOppositeEquivalence A D).inverse.map f) ↔
      moduleQuasiIso A Dᵒᵖ f := by
  let E := leftRightOppositeEquivalence A D
  let W := moduleQuasiIso A Dᵒᵖ
  change W (E.functor.map (E.inverse.map f)) ↔ W f
  calc
    W (E.functor.map (E.inverse.map f)) ↔
        W (E.functor.map (E.inverse.map f) ≫ (E.counitIso.app N).hom) :=
      (W.cancel_right_of_respectsIso _ _).symm
    _ ↔ W ((E.counitIso.app M).hom ≫ f) :=
      Iff.of_eq (congrArg (fun k => W k) (E.counitIso.hom.naturality f))
    _ ↔ W f := W.cancel_left_of_respectsIso _ _

end SerrePositivity.DifferentialGraded
