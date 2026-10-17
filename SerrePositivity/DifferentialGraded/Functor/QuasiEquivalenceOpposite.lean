module
public import SerrePositivity.DifferentialGraded.Category.OppositeHomotopy
public import SerrePositivity.DifferentialGraded.Functor.Opposite
public import SerrePositivity.DifferentialGraded.Functor.QuasiEquivalence

/-! # dg関手のoppositeによる準同値の保存

## 概要
dg関手のoppositeによる準同値の保存。

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
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]
  {E : Type w} [DGCategory A E] (F : DGFunctor A D E)

lemma homQuasiIso_op (hF : HomQuasiIso F) : HomQuasiIso F.op :=
  fun x y => hF y.unop x.unop

lemma DGFunctor.onHomotopy_op_essSurj (hF : F.onHomotopy.EssSurj) : F.op.onHomotopy.EssSurj where
  mem_essImage y := by
    let := hF
    let e := ForgetEnrichment.to (Complex A) y.as
    let Y := (toHomotopy A E).obj (ForgetEnrichment.of (Complex A) e.unop)
    let X := F.onHomotopy.objPreimage Y
    let d := ForgetEnrichment.to (Complex A) X.as
    let i := F.onHomotopy.objObjPreimageIso Y
    refine ⟨(toHomotopy A Dᵒᵖ).obj (ForgetEnrichment.of (Complex A) (Opposite.op d)), ⟨?_⟩⟩
    exact (homotopyOppositeFunctor A E).mapIso i.symm.op

lemma quasiEquivalence_op (hF : QuasiEquivalence F) : QuasiEquivalence F.op :=
  ⟨homQuasiIso_op F hF.1, F.onHomotopy_op_essSurj hF.2⟩

end SerrePositivity.DifferentialGraded
