module
public import SerrePositivity.DifferentialGraded.Module.FunctorGraphActions
public import SerrePositivity.DifferentialGraded.Tensor.BalancedElements

public import SerrePositivity.DifferentialGraded.Tensor.Parameter

/-! # graph延長と制限の評価成分

## 概要
任意の右E加群の作用をFに沿ってbalanced族へ引き戻す。

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
  (M : RightModule A E)

omit [Small.{u} D] in
lemma functorGraph_leftAction (e : E) (x y : D) :
    BalancedTensor.leftAction A D ((functorGraph A D E F).leftAt e) x y =
      BalancedTensor.leftAction A D (F.comp (leftRepresentable A e)) x y := by
  change uncurryRight ((F.map x y ≫ yonedaHom A E (F.obj x) (F.obj y)) ≫
    moduleHomπ A E (representable A (F.obj x)) (representable A (F.obj y)) e) =
      uncurryRight (F.map x y ≫ (leftRepresentable A e).map (F.obj x) (F.obj y))
  rw [Category.assoc, yonedaHom_π, endomorphismYonedaApp]

/-- 各D対象でのMの作用を使う全次数balanced族。 -/
def functorExtensionEvaluationFamily (e : E) :
    BalancedTensor.BalancedFamily A D (restrictModule A D E F.op M)
      ((functorGraph A D E F).leftAt e) (M.obj (op e)) := by
  refine ⟨fun d => BalancedTensor.rightAction A E M e (F.obj d), ?_⟩
  intro x y
  have h := (BalancedTensor.restrictFamily A D E F M (leftRepresentable A e)
    (BalancedTensor.leftYonedaFamily A E e M)).property x y
  change (BalancedTensor.rightAction A D (restrictModule A D E F.op M) x y ▷
      homObject A E e (F.obj x)) ≫ BalancedTensor.rightAction A E M e (F.obj x) =
    (α_ (M.obj (op (F.obj y))) (homObject A D x y) (homObject A E e (F.obj x))).hom ≫
      M.obj (op (F.obj y)) ◁ BalancedTensor.leftAction A D
        ((functorGraph A D E F).leftAt e) x y ≫ BalancedTensor.rightAction A E M e (F.obj y)
  rw [functorGraph_leftAction]
  exact h

/-- 延長された制限加群から元の加群への評価chain mapの各対象成分。 -/
def functorExtensionEvaluationComponent (e : E) :
    ((dgModuleExtension A D E F).obj (restrictModule A D E F.op M)).obj (op e) ⟶ M.obj (op e) :=
  BalancedTensor.desc A D _ _ (functorExtensionEvaluationFamily A D E F M e)

@[reassoc] lemma ι_functorExtensionEvaluationComponent (e : E) (d : D) :
    BalancedTensor.ι A D (restrictModule A D E F.op M) ((functorGraph A D E F).leftAt e) d ≫
      functorExtensionEvaluationComponent A D E F M e =
        BalancedTensor.rightAction A E M e (F.obj d) :=
  BalancedTensor.ι_desc A D _ _ _ d

lemma functorExtensionEvaluation_element (e : E) (d : D) {r s n : ℤ}
    (m : (M.obj (op (F.obj d))).X r) (h : GradedHom A e (F.obj d) s) (hn : r + s = n) :
    (functorExtensionEvaluationComponent A D E F M e).f n
      (BalancedTensor.element A D (restrictModule A D E F.op M)
        ((functorGraph A D E F).leftAt e) d m h hn) =
      (r * s).negOnePow • moduleAction A M h m hn := by
  have he := congrArg (fun f => f.f n
    (ιTensorObj (M.obj (op (F.obj d))) (homObject A E e (F.obj d)) r s n hn (m ⊗ₜ[A] h)))
    (ι_functorExtensionEvaluationComponent A D E F M e d)
  exact he.trans (BalancedTensor.rightAction_apply A E M e (F.obj d) r s n hn m h)

end SerrePositivity.DifferentialGraded
