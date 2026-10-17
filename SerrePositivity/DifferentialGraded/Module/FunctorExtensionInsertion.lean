module
public import SerrePositivity.DifferentialGraded.Module.FunctorExtensionEvaluation

/-! # graph延長への単位挿入成分と評価による復元

## 概要
graph延長への単位挿入成分と評価による復元。

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
open CategoryTheory MonoidalCategory Opposite HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)

/-- N(d)の元とF(d)の閉単位を、対応するtensor生成元へ送る。 -/
def functorExtensionInsertionComponent (N : RightModule A D) (d : D) :
    N.obj (op d) ⟶ ((dgModuleExtension A D E F).obj N).obj (op (F.obj d)) :=
  freeUnitInsert A (F.obj d) (N.obj (op d)) ≫
    BalancedTensor.ι A D N ((functorGraph A D E F).leftAt (F.obj d)) d

lemma functorExtensionInsertion_apply (N : RightModule A D) (d : D) (r : ℤ)
    (m : (N.obj (op d)).X r) :
    (functorExtensionInsertionComponent A D E F N d).f r m =
      BalancedTensor.element A D N ((functorGraph A D E F).leftAt (F.obj d)) d
        m (unitElement A (F.obj d)).val (add_zero r) := by
  change (BalancedTensor.ι A D N ((functorGraph A D E F).leftAt (F.obj d)) d).f r
    ((freeUnitInsert A (F.obj d) (N.obj (op d))).f r m) = _
  rw [freeUnitInsert_apply]
  rfl

/-- 制限加群の値を挿入して評価すると元に戻る。 -/
lemma functorExtensionInsertion_evaluation (M : RightModule A E) (d : D) :
    functorExtensionInsertionComponent A D E F (restrictModule A D E F.op M) d ≫
      functorExtensionEvaluationComponent A D E F M (F.obj d) = 𝟙 (M.obj (op (F.obj d))) := by
  apply chain_ext_apply
  intro r m
  rw [chain_comp_apply, functorExtensionInsertion_apply, functorExtensionEvaluation_element]
  simp only [mul_zero, Int.negOnePow_zero, one_smul]
  exact moduleAction_unit A M (op (F.obj d)) r m

end SerrePositivity.DifferentialGraded
