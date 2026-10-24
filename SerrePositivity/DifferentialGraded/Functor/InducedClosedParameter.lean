module
public import SerrePositivity.DifferentialGraded.Functor.InducedClosedConjugate
public import SerrePositivity.KST.SConstruction.DGParameterConjugation
public import SerrePositivity.KST.SConstruction.DGFunctorHomPrecomposition
/-!
概要：任意のラベル族に沿う閉共役へ、全次数パラメータ自然変換も移す。
方針：評価で前合成した元の変換へ一般の閉共役を適用し、同じ Hom 複体を保持する。
規約：KST の依存は S 構成本体を含まない dg 一般論だけ。コピー・編集を行わない。
使われ方：κ-small 提示模型の dg 関手変数における豊穣作用の一般入口。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w i j
namespace SerrePositivity.DifferentialGraded
open CategoryTheory SerrePositivity.KST.SConstruction
variable (A : Type u) [CommRing A] {C : Type v} {D : Type w}
  [DGCategory A C] [DGCategory A D] {I : Type i} {J : Type j}
  (source : I → C) (target : J → D) (F G : DGFunctor A C D)
  (objF objG : I → J)
  (eF : ∀ x, ForgetEnrichment.of (Complex A) (F.obj (source x)) ≅
    ForgetEnrichment.of (Complex A) (target (objF x)))
  (eG : ∀ x, ForgetEnrichment.of (Complex A) (G.obj (source x)) ≅
    ForgetEnrichment.of (Complex A) (target (objG x)))

/-- 同じ任意パラメータを、ラベル間の二つの実 dg 作用へ移す。 -/
def inducedDGFunctorClosedConjugateParameter {K : Complex A}
    (τ : DGFunctorParamTrans A C D K F G) :
    letI := inducedDGCategory A source
    letI := inducedDGCategory A target
    DGFunctorParamTrans A I J K
      (inducedDGFunctorClosedConjugate A source target F objF eF)
      (inducedDGFunctorClosedConjugate A source target G objG eG) := by
  letI := inducedDGCategory A source
  letI := inducedDGCategory A target
  let T := dgFunctorClosedConjugateParameter A
    ((inducedDGEvaluation A source).comp F) ((inducedDGEvaluation A source).comp G)
    (fun x => target (objF x)) (fun x => target (objG x)) eF eG
    (dgFunctorParamPre A C D I (inducedDGEvaluation A source) τ)
  exact { app := T.app, naturality := T.naturality }

end SerrePositivity.DifferentialGraded
