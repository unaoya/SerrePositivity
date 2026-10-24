module
public import SerrePositivity.DifferentialGraded.Endomorphism.ModuleConeImage
/-!
概要：加群値 dg 関手と標準 cone の実比較射を構成する。
方針：既存の Endomorphism.ModuleConeImage の同じ実比較を公開入口で再利用する。
規約：全加群型の Small 性を仮定せず、全 Hom 複体への dg 作用を使う。
使われ方：ラベル付き提示模型の cone 演算と、実 dg 加群延長の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.DGFunctor
open CategoryTheory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]
  (F : DGFunctor A (RightModule A D) (RightModule A E))
  {M N : ModuleCategory A D} (f : M ⟶ N)

def moduleValuedConeInl :
    GradedHom A (F.obj (ForgetEnrichment.to (Complex A) M))
      (F.obj (ForgetEnrichment.to (Complex A) (moduleCone A D f))) (-1) :=
  dgModuleFunctorConeInl A D E F f

lemma moduleValuedConeInl_d :
    (homObject A (RightModule A E) (F.obj (ForgetEnrichment.to (Complex A) M))
      (F.obj (ForgetEnrichment.to (Complex A) (moduleCone A D f)))).d (-1) 0
        (moduleValuedConeInl A D E F f) =
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A)
        (F.onClosed.map f ≫ F.onClosed.map (moduleConeInr A D f)))).val :=
  dgModuleFunctorConeInl_d A D E F f

def moduleValuedConeComparison :
    moduleCone A E (F.onClosed.map f) ⟶ F.onClosed.obj (moduleCone A D f) :=
  dgModuleFunctorConeComparison A D E F f

lemma moduleValuedConeComparison_eval (x : E) :
    (moduleEvaluation A E x).map (moduleValuedConeComparison A D E F f) =
      moduleConeImageComparison A D (F.comp (moduleEvaluationDG A E x)) f :=
  dgModuleFunctorConeComparison_eval A D E F f x

instance moduleValuedConeComparison_isIso :
    IsIso (moduleValuedConeComparison A D E F f) :=
  dgModuleFunctorConeComparison_isIso A D E F f

/-- 加群値 dg 関手は、同じ実 cone と全評価の標準比較によって可換する。 -/
def moduleValuedConeIso :
    moduleCone A E (F.onClosed.map f) ≅ F.onClosed.obj (moduleCone A D f) :=
  dgModuleFunctorConeIso A D E F f

end SerrePositivity.DifferentialGraded.DGFunctor
