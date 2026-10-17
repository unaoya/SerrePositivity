module
public import SerrePositivity.DifferentialGraded.Module.FunctorExtensionEvaluation
public import SerrePositivity.DifferentialGraded.Tensor.BimoduleRightElements
public import SerrePositivity.DifferentialGraded.Tensor.ElementMap

/-! # graph tensorの評価と右作用の整合性

## 概要
任意次数の生成元上で二つのKoszul符号を比較し、全Hom自然な閉零射へ束ねる。

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
open CategoryTheory MonoidalCategory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)

lemma dgModuleExtension_action_element (N : RightModule A D) (x y : Eᵒᵖ) (d : D)
    {p r s a j n : ℤ} (ha : r + s = a) (hj : s + p = j) (hn : a + p = n)
    (f : GradedHom A x y p) (m : (N.obj (op d)).X r) (h : GradedHom A x.unop (F.obj d) s) :
    moduleAction A ((dgModuleExtension A D E F).obj N) f
      (BalancedTensor.element A D N ((functorGraph A D E F).leftAt x.unop) d m h ha) hn =
      (p * r).negOnePow • BalancedTensor.element A D N
        ((functorGraph A D E F).leftAt y.unop) d m
        (moduleAction A (representable A (F.obj d)) f h hj) (by omega) :=
  BimoduleTensor.compose_rightAction_element A E D (RightModule A D)
    (functorGraph A D E F) (DGFunctor.id (RightModule A D)) x y d N ha hj hn f m h

variable (M : RightModule A E)

omit [Small.{u} D] [Small.{u} E] in
lemma functorExtensionEvaluation_action (x y : Eᵒᵖ) (d : D) {p r s n : ℤ}
    (f : GradedHom A x y p) (m : (M.obj (op (F.obj d))).X r)
    (h : GradedHom A x.unop (F.obj d) s) (hn : r + s + p = n) :
    (p * r).negOnePow • ((r * (s + p)).negOnePow •
      moduleAction A M (moduleAction A (representable A (F.obj d)) f h rfl) m (by omega)) =
      moduleAction A M f ((r * s).negOnePow • moduleAction A M h m rfl) hn := by
  have hc := moduleAction_representable A (F.obj d) M x y p s r (s + p) n (r + s)
    rfl rfl (by omega) f h m
  rw [hc, moduleAction_units_smul]
  simp only [smul_smul]
  congr 1
  rw [← Int.negOnePow_add]
  have hi : p * r + r * (s + p) = r * s + 2 * (p * r) := by ring
  rw [hi, Int.negOnePow_add, Int.negOnePow_two_mul, mul_one]

lemma functorExtensionEvaluation_naturality (x y : Eᵒᵖ) :
    ((dgModuleExtension A D E F).obj (restrictModule A D E F.op M)).map x y ≫
        homPostcompose _ (functorExtensionEvaluationComponent A D E F M y.unop) =
      M.map x y ≫ homPrecompose (functorExtensionEvaluationComponent A D E F M x.unop) _ := by
  apply BalancedTensor.homMap_post_pre_eq A D (restrictModule A D E F.op M)
    ((functorGraph A D E F).leftAt x.unop)
  intro p f d r s a n ha hn m h
  subst a
  change (functorExtensionEvaluationComponent A D E F M y.unop).f n
    (moduleAction A ((dgModuleExtension A D E F).obj (restrictModule A D E F.op M)) f
      (BalancedTensor.element A D (restrictModule A D E F.op M)
        ((functorGraph A D E F).leftAt x.unop) d m h rfl) hn) = _
  rw [dgModuleExtension_action_element A D E F _ x y d rfl rfl hn]
  simp only [Units.smul_def, map_zsmul]
  change (p * r).negOnePow • (functorExtensionEvaluationComponent A D E F M y.unop).f n
    (BalancedTensor.element A D (restrictModule A D E F.op M)
      ((functorGraph A D E F).leftAt y.unop) d m
        (moduleAction A (representable A (F.obj d)) f h rfl) (by omega)) =
    moduleAction A M f ((functorExtensionEvaluationComponent A D E F M x.unop).f (r + s)
      (BalancedTensor.element A D (restrictModule A D E F.op M)
        ((functorGraph A D E F).leftAt x.unop) d m h rfl)) hn
  rw [functorExtensionEvaluation_element, functorExtensionEvaluation_element]
  exact functorExtensionEvaluation_action A D E F M x y d f m h hn

/-- 延長された制限加群から元の加群への実際の全Hom自然な閉零射。 -/
def functorExtensionCounit :
    ForgetEnrichment.of (Complex A)
      ((dgModuleExtension A D E F).obj (restrictModule A D E F.op M)) ⟶
        ForgetEnrichment.of (Complex A) M :=
  moduleMorphismMk A E (fun e => functorExtensionEvaluationComponent A D E F M e.unop)
    (functorExtensionEvaluation_naturality A D E F M)

lemma functorExtensionCounit_eval (e : E) :
    (moduleEvaluation A E e).map (functorExtensionCounit A D E F M) =
      functorExtensionEvaluationComponent A D E F M e := moduleMorphismMk_eval A E _ _ e

end SerrePositivity.DifferentialGraded
