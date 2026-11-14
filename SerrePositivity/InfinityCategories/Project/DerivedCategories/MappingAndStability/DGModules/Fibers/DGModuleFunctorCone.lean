module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.DGFunctors.DGFunctorClosedCycles
public import SerrePositivity.DifferentialGraded.Module.ConeConstruction
public import SerrePositivity.DifferentialGraded.Functor.ModuleShift

/-! # dg 加群間の dg 関手による実 cone 比較

概要：任意の dg 加群値 dg 関手に対し、写した射の cone から元の cone の像への射を作る。
方針：次数 −1 の左包含の像の微分を照合し、全 dg 自然な cone 延長に入力する。
規約：平坦性を仮定しない。使われ方：実 cofiber 四角形の保存。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]
variable (F : DGFunctor A (RightModule A D) (RightModule A E))
variable {M N : ModuleCategory A D}

/-- 元の cone の次数 −1 包含の実 dg 関手による像。 -/
def dgModuleFunctorConeInl (f : M ⟶ N) :
    GradedHom A (F.obj (ForgetEnrichment.to (Complex A) M))
      (F.obj (ForgetEnrichment.to (Complex A) (moduleCone A D f))) (-1) :=
  (F.map (ForgetEnrichment.to (Complex A) M)
    (ForgetEnrichment.to (Complex A) (moduleCone A D f))).f (-1) (moduleConeInlElement A D f)

/-- 左包含の像の微分は、写した射と写した右包含の合成。 -/
lemma dgModuleFunctorConeInl_d (f : M ⟶ N) :
    (moduleHom A E (F.obj (ForgetEnrichment.to (Complex A) M))
      (F.obj (ForgetEnrichment.to (Complex A) (moduleCone A D f)))).d (-1) 0
        (dgModuleFunctorConeInl A D E F f) =
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A)
        (F.onClosed.map f ≫ F.onClosed.map (moduleConeInr A D f)))).val := by
  have hc := ConcreteCategory.congr_hom
    ((F.map (ForgetEnrichment.to (Complex A) M)
      (ForgetEnrichment.to (Complex A) (moduleCone A D f))).comm (-1) 0)
    (moduleConeInlElement A D f)
  change _ = (F.map (ForgetEnrichment.to (Complex A) M)
    (ForgetEnrichment.to (Complex A) (moduleCone A D f))).f 0
      ((moduleHom A D (ForgetEnrichment.to (Complex A) M)
        (ForgetEnrichment.to (Complex A) (moduleCone A D f))).d (-1) 0
          (moduleConeInlElement A D f)) at hc
  rw [moduleConeInlElement_d, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctor_mapClosedCycle, Functor.map_comp] at hc
  exact hc

/-- 全 Hom end 内の零ホモトピーから作る cone の実比較射。 -/
def dgModuleFunctorConeComparison (f : M ⟶ N) :
    moduleCone A E (F.onClosed.map f) ⟶ F.onClosed.obj (moduleCone A D f) :=
  moduleConeDescOfBoundary A E (F.onClosed.map f) (dgModuleFunctorConeInl A D E F f)
    (F.onClosed.map (moduleConeInr A D f)) (dgModuleFunctorConeInl_d A D E F f)

/-- 実比較射は右包含と厳密に整合する。 -/
lemma dgModuleFunctorConeComparison_inr (f : M ⟶ N) :
    moduleConeInr A E (F.onClosed.map f) ≫ dgModuleFunctorConeComparison A D E F f =
      F.onClosed.map (moduleConeInr A D f) :=
  moduleConeDescOfBoundary_inr A E _ _ _ _

/-- 実比較射の各評価は既存の複体値 dg 関手の cone 比較射である。 -/
lemma dgModuleFunctorConeComparison_eval (f : M ⟶ N) (x : E) :
    (moduleEvaluation A E x).map (dgModuleFunctorConeComparison A D E F f) =
      DGFunctor.moduleConeImageComparison A D (F.comp (moduleEvaluationDG A E x)) f := by
  rw [dgModuleFunctorConeComparison, moduleConeDescOfBoundary_eval]
  rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories
