module
public import SerrePositivity.DifferentialGraded.Module.FunctorExtension
public import SerrePositivity.DifferentialGraded.Tensor.Graded

/-! # graph延長の閉零射とtensor生成元上の計算

## 概要
graph延長の閉零射とtensor生成元上の計算。

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
open CategoryTheory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)

lemma dgModuleExtension_map_π (M N : RightModule A D) (e : E) :
    (dgModuleExtension A D E F).map M N ≫
      moduleHomπ A E ((dgModuleExtension A D E F).obj M)
        ((dgModuleExtension A D E F).obj N) e =
      BalancedTensor.rightHomMap A D M N ((functorGraph A D E F).leftAt e) := by
  have h := BimoduleTensor.compose_leftMap_π A E D (RightModule A D) (functorGraph A D E F)
      (DGFunctor.id (RightModule A D)) M N e
  change (dgModuleExtension A D E F).map M N ≫
    moduleHomπ A E ((dgModuleExtension A D E F).obj M)
      ((dgModuleExtension A D E F).obj N) e =
    𝟙 _ ≫ BalancedTensor.rightHomMap A D M N ((functorGraph A D E F).leftAt e) at h
  exact h.trans (Category.id_comp _)

lemma dgModuleExtension_map_eval {M N : ModuleCategory A D} (f : M ⟶ N) (e : E) :
    (moduleEvaluation A E e).map ((dgModuleExtension A D E F).onClosed.map f) =
      BalancedTensor.rightTensorMap A D ((functorGraph A D E F).leftAt e) f := by
  apply Cochain.ofHom_injective
  rw [moduleEvaluation_cochain]
  change (moduleHomπ A E _ _ e).f 0
    (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) f ≫
      (dgModuleExtension A D E F).map _ _)).val = _
  rw [cycleFromUnit_postcomp]
  have h := congrArg (fun k => k.f 0 (cycleFromUnit _
    (ForgetEnrichment.homTo (Complex A) f)).val)
      (dgModuleExtension_map_π A D E F (ForgetEnrichment.to (Complex A) M)
        (ForgetEnrichment.to (Complex A) N) e)
  exact h.trans (BalancedTensor.rightHomMap_closedElement A D
    ((functorGraph A D E F).leftAt e) f)

lemma dgModuleExtension_map_eval_element {M N : ModuleCategory A D} (f : M ⟶ N)
    (e : E) (d : D) {r s n : ℤ}
    (m : ((ForgetEnrichment.to (Complex A) M).obj (op d)).X r)
    (h : GradedHom A e (F.obj d) s) (hn : r + s = n) :
    ((moduleEvaluation A E e).map ((dgModuleExtension A D E F).onClosed.map f)).f n
      (BalancedTensor.element A D (ForgetEnrichment.to (Complex A) M)
        ((functorGraph A D E F).leftAt e) d m h hn) =
      BalancedTensor.element A D (ForgetEnrichment.to (Complex A) N)
        ((functorGraph A D E F).leftAt e) d (((moduleEvaluation A D d).map f).f r m) h hn := by
  have he := congrArg (fun k => k.f n
    (BalancedTensor.element A D (ForgetEnrichment.to (Complex A) M)
      ((functorGraph A D E F).leftAt e) d m h hn)) (dgModuleExtension_map_eval A D E F f e)
  exact he.trans (BalancedTensor.rightTensorMap_element A D
    ((functorGraph A D E F).leftAt e) f d m h hn)

end SerrePositivity.DifferentialGraded
