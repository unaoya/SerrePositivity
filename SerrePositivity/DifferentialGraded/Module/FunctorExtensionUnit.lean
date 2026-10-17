module
public import SerrePositivity.DifferentialGraded.Module.FunctorExtensionInsertion
public import SerrePositivity.DifferentialGraded.Module.FunctorExtensionCounit
public import SerrePositivity.DifferentialGraded.Tensor.BalancedUnitElements

/-! # graph延長–制限の全Hom自然な単位射 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)

omit [Small.{u} D] in
lemma functorGraph_leftAction_unit (x y : D) {p : ℤ} (f : GradedHom A x y p) :
    leftAction A ((functorGraph A D E F).leftAt (F.obj x)) f
      (unitElement A (F.obj x)).val (zero_add p) = (F.map x y).f p f := by
  change (((F.map x y ≫ yonedaHom A E (F.obj x) (F.obj y)) ≫
    moduleHomπ A E (representable A (F.obj x)) (representable A (F.obj y))
      (F.obj x)).f p f).v 0 p (zero_add p) (unitElement A (F.obj x)).val = _
  rw [Category.assoc, yonedaHom_π, endomorphismYonedaApp]
  change leftAction A (leftRepresentable A (F.obj x)) ((F.map x y).f p f)
    (unitElement A (F.obj x)).val (zero_add p) = _
  rw [leftRepresentable_action, mul_zero, Int.negOnePow_zero, one_smul, forward_unit]

lemma functorExtensionInsertion_action (N : RightModule A D) (x y : Dᵒᵖ)
    {p r n : ℤ} (f : GradedHom A x y p) (m : (N.obj x).X r) (hn : r + p = n) :
    (functorExtensionInsertionComponent A D E F N y.unop).f n
      (moduleAction A N f m hn) =
    moduleAction A (restrictModule A D E F.op ((dgModuleExtension A D E F).obj N)) f
      ((functorExtensionInsertionComponent A D E F N x.unop).f r m) hn := by
  subst n
  have hn : r + p = r + p := rfl
  rw [functorExtensionInsertion_apply, functorExtensionInsertion_apply, restrictModule_action]
  rw [dgModuleExtension_action_element A D E F N (op (F.obj x.unop))
    (op (F.obj y.unop)) x.unop (add_zero r) (zero_add p) hn]
  rw [representable_action, unit_forward]
  have hb := BalancedTensor.element_balanced_zero A D N
    ((functorGraph A D E F).leftAt (F.obj y.unop)) y.unop x.unop m f
      (unitElement A (F.obj y.unop)).val
  have hu := functorGraph_leftAction_unit A D E F y.unop x.unop f
  change leftAction A ((functorGraph A D E F).leftAt (F.obj y.unop)) f
    (unitElement A (F.obj y.unop)).val (by omega) = (F.map y.unop x.unop).f p f at hu
  have hbb : (r * p).negOnePow • BalancedTensor.element A D N
      ((functorGraph A D E F).leftAt (F.obj y.unop)) y.unop
        (moduleAction A N f m hn) (unitElement A (F.obj y.unop)).val (add_zero (r + p)) =
    BalancedTensor.element A D N ((functorGraph A D E F).leftAt (F.obj y.unop)) x.unop m
      ((F.map y.unop x.unop).f p f) hn := by
    exact hb.trans (congrArg (fun z => BalancedTensor.element A D N
      ((functorGraph A D E F).leftAt (F.obj y.unop)) x.unop m z
        (by omega : r + p = r + p)) hu)
  have hc := congrArg (fun z => (r * p).negOnePow • z) hbb
  rw [smul_smul, Int.units_mul_self, one_smul] at hc
  change BalancedTensor.element A D N ((functorGraph A D E F).leftAt (F.obj y.unop))
    y.unop (moduleAction A N f m rfl) (unitElement A (F.obj y.unop)).val (add_zero (r + p)) =
    (p * r).negOnePow • BalancedTensor.element A D N
      ((functorGraph A D E F).leftAt (F.obj y.unop)) x.unop m
        ((F.map y.unop x.unop).f p f) rfl
  rw [mul_comm r p] at hc
  exact hc

/-- 各対象への単位挿入を全Hom自然な閉零加群射に束ねる。 -/
def functorExtensionUnit (N : RightModule A D) :
    ForgetEnrichment.of (Complex A) N ⟶ ForgetEnrichment.of (Complex A)
      (restrictModule A D E F.op ((dgModuleExtension A D E F).obj N)) :=
  moduleMorphismMk A D (fun x => functorExtensionInsertionComponent A D E F N x.unop)
    (closedFamily_of_action A _ (fun x y _ _ _ hn f m =>
      functorExtensionInsertion_action A D E F N x y f m hn))

lemma functorExtensionUnit_eval (N : RightModule A D) (d : D) :
    (moduleEvaluation A D d).map (functorExtensionUnit A D E F N) =
      functorExtensionInsertionComponent A D E F N d := moduleMorphismMk_eval A D _ _ d

end SerrePositivity.DifferentialGraded
