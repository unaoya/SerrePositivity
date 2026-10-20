module
public import SerrePositivity.KST.SConstruction.PerfectDGExtensionParameter
public import SerrePositivity.KST.SConstruction.DGParameterConjugation
public import SerrePositivity.KST.SConstruction.DGFunctorHomPrecomposition
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGAction

/-! # ラベル付き Perf の全パラメータ作用
概要：元の入力の K 自然変換を、ラベル付き作用間の全次数自然変換へ送る。
方針：元の実 Perf 作用を評価で前合成し、元の閉零合成比較で両端を共役する。
規約：ラベル対象全体の end を作らない。使われ方：単体的豊穣 Perf 作用の高次成分。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) (E : Type w)
  [DGCategory A D] [Small.{u} D] [DGCategory A E] [Small.{u} E]

/-- 任意 K の入力自然変換の、実 Perf 内で評価したラベル作用。 -/
def presentedPerfectDGParameterEvaluated {K : Complex A} {F G : DGFunctor A D E}
    (τ : DGFunctorParamTrans A D E K F G) :
    DGFunctorParamTrans A (PresentedPerfectDGObject A D) (PerfectDGModule A E) K
      (presentedPerfectDGActionEvaluated A D E F) (presentedPerfectDGActionEvaluated A D E G) :=
  dgFunctorClosedConjugateParameter A
    ((presentedPerfectDGEvaluation A D).comp (perfectDGExtension A D E F))
    ((presentedPerfectDGEvaluation A D).comp (perfectDGExtension A D E G))
    (fun X => presentedPerfectDGValue A E (presentedPerfectDGActionObject A D E F X))
    (fun X => presentedPerfectDGValue A E (presentedPerfectDGActionObject A D E G X))
    (presentedPerfectDGActionIso A D E F) (presentedPerfectDGActionIso A D E G)
    (dgFunctorParamPre A (PerfectDGModule A D) (PerfectDGModule A E)
      (PresentedPerfectDGObject A D) (presentedPerfectDGEvaluation A D)
      (perfectDGExtensionParameter A D E τ))

/-- 任意 K の入力自然変換は、元のラベル付き dg 作用間の全次数自然変換を与える。 -/
def presentedPerfectDGParameter {K : Complex A} {F G : DGFunctor A D E}
    (τ : DGFunctorParamTrans A D E K F G) :
    DGFunctorParamTrans A (PresentedPerfectDGObject A D) (PresentedPerfectDGObject A E) K
      (presentedPerfectDGAction A D E F) (presentedPerfectDGAction A D E G) where
  app := (presentedPerfectDGParameterEvaluated A D E τ).app
  naturality := (presentedPerfectDGParameterEvaluated A D E τ).naturality

/-- 全 Hom 成分は元の実 Perf パラメータ作用を同じ合成比較で共役したもの。 -/
lemma presentedPerfectDGParameter_app {K : Complex A} {F G : DGFunctor A D E}
    (τ : DGFunctorParamTrans A D E K F G) (X : PresentedPerfectDGObject A D) :
    (presentedPerfectDGParameter A D E τ).app X =
      (perfectDGExtensionParameter A D E τ).app (presentedPerfectDGValue A D X) ≫
        enrichedClosedIsoConjugation (Complex A)
          (presentedPerfectDGActionIso A D E F X) (presentedPerfectDGActionIso A D E G X) := rfl

end SerrePositivity.KST.SConstruction
