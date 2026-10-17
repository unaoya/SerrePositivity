module
public import SerrePositivity.DifferentialGraded.Endomorphism.GradedSplitImage
public import SerrePositivity.DifferentialGraded.Functor.ModuleConeIso
public import SerrePositivity.DifferentialGraded.Module.ConeHomotopyDesc
public import SerrePositivity.DifferentialGraded.Module.EvaluationReflects

/-! # 加群値dg関手による標準coneの実際の比較同型 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) (B : Type w)
  [DGCategory A D] [DGCategory A B] [Small.{u} D] [Small.{u} B]
variable (F : DGFunctor A (RightModule A D) (RightModule A B))

/-- coneの次数−1包含を全Hom写像で送る。 -/
def dgModuleFunctorConeInl {M N : ModuleCategory A D} (f : M ⟶ N) :
    (moduleHom A B (F.obj (ForgetEnrichment.to (Complex A) M))
      (F.obj (ForgetEnrichment.to (Complex A) (moduleCone A D f)))).X (-1) :=
  (F.map (ForgetEnrichment.to (Complex A) M)
    (ForgetEnrichment.to (Complex A) (moduleCone A D f))).f (-1) (moduleConeInlElement A D f)

lemma dgModuleFunctorConeInl_d {M N : ModuleCategory A D} (f : M ⟶ N) :
    (moduleHom A B (F.obj (ForgetEnrichment.to (Complex A) M))
        (F.obj (ForgetEnrichment.to (Complex A) (moduleCone A D f)))).d (-1) 0
        (dgModuleFunctorConeInl A D B F f) =
      endomorphismClosedElement A B (F.onClosed.map f ≫ F.onClosed.map (moduleConeInr A D f)) := by
  have hd := congrArg (fun k => k (moduleConeInlElement A D f))
    ((F.map (ForgetEnrichment.to (Complex A) M)
      (ForgetEnrichment.to (Complex A) (moduleCone A D f))).comm (-1) 0)
  have he := congrArg
    ((F.map (ForgetEnrichment.to (Complex A) M)
      (ForgetEnrichment.to (Complex A) (moduleCone A D f))).f 0)
    (moduleConeInlElement_d A D f)
  have hc := dgModuleFunctor_closedElement A D B F (f ≫ moduleConeInr A D f)
  rw [CategoryTheory.Functor.map_comp] at hc
  exact hd.trans (he.trans hc)

/-- 閉零加群射としてのcone比較。全次数作用に関して自然。 -/
def dgModuleFunctorConeComparison {M N : ModuleCategory A D} (f : M ⟶ N) :
    moduleCone A B (F.onClosed.map f) ⟶ F.onClosed.obj (moduleCone A D f) :=
  moduleConeDescOfBoundary A B (F.onClosed.map f) (dgModuleFunctorConeInl A D B F f)
    (F.onClosed.map (moduleConeInr A D f)) (dgModuleFunctorConeInl_d A D B F f)

lemma dgModuleFunctorConeComparison_eval {M N : ModuleCategory A D} (f : M ⟶ N) (b : B) :
    (moduleEvaluation A B b).map (dgModuleFunctorConeComparison A D B F f) =
      DGFunctor.moduleConeImageComparison A D (F.comp (moduleEvaluationDG A B b)) f := by
  unfold dgModuleFunctorConeComparison
  rw [moduleConeDescOfBoundary_eval]
  rfl

instance dgModuleFunctorConeComparison_isIso {M N : ModuleCategory A D} (f : M ⟶ N) :
    IsIso (dgModuleFunctorConeComparison A D B F f) :=
  moduleIsIso_of_evaluations A B _ (fun b => by
    rw [dgModuleFunctorConeComparison_eval]
    infer_instance)

/-- 任意の主加群値dg関手は主加群coneを、実際の加群同型まで保つ。 -/
def dgModuleFunctorConeIso {M N : ModuleCategory A D} (f : M ⟶ N) :
    moduleCone A B (F.onClosed.map f) ≅ F.onClosed.obj (moduleCone A D f) :=
  asIso (dgModuleFunctorConeComparison A D B F f)

lemma dgModuleFunctorConeComparison_inr {M N : ModuleCategory A D} (f : M ⟶ N) :
    moduleConeInr A B (F.onClosed.map f) ≫ dgModuleFunctorConeComparison A D B F f =
      F.onClosed.map (moduleConeInr A D f) :=
  moduleConeDescOfBoundary_inr A B _ _ _ _

end SerrePositivity.DifferentialGraded
