module
public import SerrePositivity.DifferentialGraded.Functor.DGFunctorHomPostcomposition
public import SerrePositivity.DifferentialGraded.Module.FreeSphere
public import SerrePositivity.DifferentialGraded.Bimodule.Value

/-! # 元の dg 関手の全パラメータの graph 作用
概要：K パラメータ付き dg 自然変換を、元の graph bimodule の変換へ送る。
方針：実 dg Yoneda 関手の全 Hom 作用で後合成する。
規約：パラメータと全次数を保持する。使われ方：高次入力の実加群延長への作用。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) (E : Type w)
  [DGCategory A D] [DGCategory A E] [Small.{u} E]

/-- 元の全パラメータ付き自然変換を graph の全 dg 自然変換へ送る。 -/
def dgFunctorGraphParameter {K : Complex A} {F G : DGFunctor A D E}
    (τ : DGFunctorParamTrans A D E K F G) :
    BimoduleParamTrans A E D K (functorGraph A D E F) (functorGraph A D E G) :=
  dgFunctorParamPost A D E (RightModule A E) (dgYoneda A E) τ

/-- graph 変換の成分は元の自然変換の成分の実 Yoneda 像。 -/
lemma dgFunctorGraphParameter_app {K : Complex A} {F G : DGFunctor A D E}
    (τ : DGFunctorParamTrans A D E K F G) (d : D) :
    (dgFunctorGraphParameter A D E τ).app d =
      τ.app d ≫ yonedaHom A E (F.obj d) (G.obj d) := rfl

/-- graph 変換の両対象評価は同じ元の Hom chain map を回収する。 -/
lemma dgFunctorGraphParameter_value {K : Complex A} {F G : DGFunctor A D E}
    (τ : DGFunctorParamTrans A D E K F G) (e : E) (d : D) :
    Bimodule.paramValue A E D (dgFunctorGraphParameter A D E τ) e d =
      (τ.app d ≫ yonedaHom A E (F.obj d) (G.obj d)) ≫
        moduleHomπ A E (representable A (F.obj d)) (representable A (G.obj d)) e := rfl

/-- graph の斉次作用は、元の入力成分の合成と Yoneda の交差符号を保持する。 -/
lemma dgFunctorGraphParameter_element {K : Complex A} {F G : DGFunctor A D E}
    (τ : DGFunctorParamTrans A D E K F G) (e : E) (d : D)
    {k s n : ℤ} (t : K.X k) (x : GradedHom A e (F.obj d) s) (hn : s + k = n) :
    (((Bimodule.paramValue A E D (dgFunctorGraphParameter A D E τ) e d).f k t).v s n hn) x =
      (k * s).negOnePow • forward A x ((τ.app d).f k t) hn :=
  yonedaHom_element A E (F.obj d) (G.obj d) e ((τ.app d).f k t) x hn

end SerrePositivity.KST.SConstruction
