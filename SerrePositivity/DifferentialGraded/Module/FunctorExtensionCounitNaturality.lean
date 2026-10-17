module
public import SerrePositivity.DifferentialGraded.Module.FunctorExtensionCounit
public import SerrePositivity.DifferentialGraded.Module.FunctorExtensionMaps

/-! # graph延長–制限の余単位の加群変数に関する自然性

## 概要
graph延長–制限の余単位の加群変数に関する自然性。

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

def dgModuleCounit :
    moduleRestriction A D E F.op ⋙ (dgModuleExtension A D E F).onClosed ⟶
      𝟭 (ModuleCategory A E) where
  app M := functorExtensionCounit A D E F (ForgetEnrichment.to (Complex A) M)
  naturality {M N} f := by
    apply moduleMorphism_ext
    intro e
    rw [Functor.map_comp, Functor.map_comp, functorExtensionCounit_eval,
      functorExtensionCounit_eval]
    simp only [CategoryTheory.Functor.comp_map, CategoryTheory.Functor.id_map]
    rw [dgModuleExtension_map_eval]
    apply Cochain.ofHom_injective
    apply BalancedTensor.cochain_zero_element_ext A D
      (restrictModule A D E F.op (ForgetEnrichment.to (Complex A) M))
      ((functorGraph A D E F).leftAt e)
    intro d r s n hn m h
    simp only [Cochain.ofHom_v]
    change (functorExtensionEvaluationComponent A D E F
      (ForgetEnrichment.to (Complex A) N) e).f n
      ((BalancedTensor.rightTensorMap A D ((functorGraph A D E F).leftAt e)
        ((moduleRestriction A D E F.op).map f)).f n
        (BalancedTensor.element A D (restrictModule A D E F.op
          (ForgetEnrichment.to (Complex A) M)) ((functorGraph A D E F).leftAt e) d m h hn)) =
      ((moduleEvaluation A E e).map f).f n
        ((functorExtensionEvaluationComponent A D E F
          (ForgetEnrichment.to (Complex A) M) e).f n
          (BalancedTensor.element A D (restrictModule A D E F.op
            (ForgetEnrichment.to (Complex A) M)) ((functorGraph A D E F).leftAt e) d m h hn))
    refine (congrArg (fun z => (functorExtensionEvaluationComponent A D E F
      (ForgetEnrichment.to (Complex A) N) e).f n z)
      (BalancedTensor.rightTensorMap_element A D ((functorGraph A D E F).leftAt e)
        ((moduleRestriction A D E F.op).map f) d m h hn)).trans ?_
    rw [moduleRestriction_map_eval]
    change (functorExtensionEvaluationComponent A D E F
      (ForgetEnrichment.to (Complex A) N) e).f n
      (BalancedTensor.element A D (restrictModule A D E F.op
        (ForgetEnrichment.to (Complex A) N)) ((functorGraph A D E F).leftAt e) d
        (((moduleEvaluation A E (F.obj d)).map f).f r m) h hn) =
      ((moduleEvaluation A E e).map f).f n
        ((functorExtensionEvaluationComponent A D E F
          (ForgetEnrichment.to (Complex A) M) e).f n
          (BalancedTensor.element A D (restrictModule A D E F.op
            (ForgetEnrichment.to (Complex A) M)) ((functorGraph A D E F).leftAt e) d m h hn))
    rw [functorExtensionEvaluation_element, functorExtensionEvaluation_element]
    simp only [Units.smul_def, map_zsmul]
    have ha := closedFamily_action A
      (fun x : Eᵒᵖ => (moduleEvaluation A E x.unop).map f)
      (fun x y => closedTransApp_naturality A (moduleClosedHomEquiv A E M N f) x y)
      (op (F.obj d)) (op e) s r n hn h m
    exact congrArg (fun z => ((r * s).negOnePow : ℤ) • z) ha.symm

end SerrePositivity.DifferentialGraded
