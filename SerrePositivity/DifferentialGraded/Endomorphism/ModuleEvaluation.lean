module
public import SerrePositivity.DifferentialGraded.Endomorphism.ModuleTensorElements
public import SerrePositivity.DifferentialGraded.Tensor.HomAdjunctionFamilies
public import SerrePositivity.DifferentialGraded.Tensor.ElementMap

/-! # 再構成tensorから元のdg加群への評価射

各D成分のbalanced評価を、全次数のD自然性を持つ実際のdg加群射に組み立てる。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (E M : RightModule A D)

/-- End(E)でbalancedな、Eの各成分におけるHomの評価。 -/
def endomorphismModuleEvaluationFamily (d : D) :
    BalancedTensor.BalancedFamily A (EndomorphismObject E)
      ((endomorphismModuleHom A D E).obj M) ((endomorphismModuleAction A D E).leftAt d)
      (M.obj (op d)) := by
  apply BalancedTensor.balancedFamilyMk A (EndomorphismObject E)
    (M := (endomorphismModuleHom A D E).obj M)
    (N := (endomorphismModuleAction A D E).leftAt d)
    (fun _ => uncurryRight (moduleHomπ A D E M d))
  intro x y r p s n hn m f t
  change (moduleHom A D E M).X r at m
  change (moduleHom A D E E).X p at f
  change (E.obj (op d)).X s at t
  change (r * p).negOnePow • (uncurryRight (moduleHomπ A D E M d)).f n
    (ιTensorObj (moduleHom A D E M) (E.obj (op d)) (r + p) s n hn
      (moduleAction A ((endomorphismModuleHom A D E).obj M)
        (x := op y) (y := op x) f m rfl ⊗ₜ[A] t)) =
    (uncurryRight (moduleHomπ A D E M d)).f n
      (ιTensorObj (moduleHom A D E M) (E.obj (op d)) r (p + s) n (by omega)
        (m ⊗ₜ[A] leftAction A ((endomorphismModuleAction A D E).leftAt d)
          (x := x) (y := y) f t (by omega)))
  rw [uncurryRight_apply, uncurryRight_apply]
  change (r * p).negOnePow •
      ((moduleHomπ A D E M d).f (r + p)
        (forward A (D := RightModule A D) (x := E) (y := E) (z := M) f m (by omega))).v
          s n (by omega) t =
    ((moduleHomπ A D E M d).f r m).v (p + s) n (by omega)
      (((moduleHomπ A D E E d).f p f).v s (p + s) (by omega) t)
  rw [moduleHomForward_π, Cochain.units_smul_v,
    Cochain.comp_v _ _ _ s (p + s) n (by omega) (by omega)]
  change (r * p).negOnePow • ((p * r).negOnePow •
    (((moduleHomπ A D E M d).f r m).v (p + s) n (by omega)
      (((moduleHomπ A D E E d).f p f).v s (p + s) (by omega) t))) = _
  rw [mul_comm r p, smul_smul, Int.units_mul_self, one_smul]

/-- 各D成分での再構成評価。 -/
def endomorphismModuleEvaluationComponent (d : D) :
    ((endomorphismModuleTensor A D E).obj ((endomorphismModuleHom A D E).obj M)).obj (op d) ⟶
      M.obj (op d) :=
  BalancedTensor.desc A _ _ _ (endomorphismModuleEvaluationFamily A D E M d)

lemma endomorphismModuleEvaluation_element (d : D) {r s n : ℤ}
    (m : (moduleHom A D E M).X r) (t : (E.obj (op d)).X s) (hn : r + s = n) :
    (endomorphismModuleEvaluationComponent A D E M d).f n
      (BalancedTensor.element A (EndomorphismObject E) ((endomorphismModuleHom A D E).obj M)
        ((endomorphismModuleAction A D E).leftAt d) .point m t hn) =
      ((moduleHomπ A D E M d).f r m).v s n (by omega) t := by
  have h := BalancedTensor.element_postcompose A (EndomorphismObject E)
    ((endomorphismModuleHom A D E).obj M) ((endomorphismModuleAction A D E).leftAt d) .point
    (endomorphismModuleEvaluationComponent A D E M d) (uncurryRight (moduleHomπ A D E M d))
    (BalancedTensor.ι_desc A _ _ _ (endomorphismModuleEvaluationFamily A D E M d) .point) m t hn
  exact h.trans (uncurryRight_apply (moduleHomπ A D E M d) r s n hn m t)

/-- Hom endの自然性による、評価とD作用の交換式。 -/
lemma endomorphismModuleEvaluation_action (x y : Dᵒᵖ) {p r s n : ℤ}
    (f : GradedHom A x y p) (m : (moduleHom A D E M).X r) (t : (E.obj x).X s)
    (hn : r + s + p = n) :
    (p * r).negOnePow • ((moduleHomπ A D E M y.unop).f r m).v (p + s) n (by omega)
        (moduleAction A E (x := x) (y := y) f t (by omega)) =
      moduleAction A M (x := x) (y := y) f
        (((moduleHomπ A D E M x.unop).f r m).v s (r + s) (by omega) t) (by omega) := by
  have h := congrArg (fun c => c.v s n (by omega) t)
    (moduleHomElement_naturality A D r m x y p f)
  rw [Cochain.comp_v _ _ _ s (p + s) n (by omega) (by omega), Cochain.units_smul_v,
    Cochain.comp_v _ _ _ s (r + s) n (by omega) (by omega)] at h
  change ((moduleHomπ A D E M y.unop).f r m).v (p + s) n (by omega)
      (moduleAction A E (x := x) (y := y) f t (by omega)) =
    (r * p).negOnePow • moduleAction A M (x := x) (y := y) f
      (((moduleHomπ A D E M x.unop).f r m).v s (r + s) (by omega) t) (by omega) at h
  rw [h, mul_comm p r, smul_smul, Int.units_mul_self, one_smul]

/-- 各成分の評価は全次数のD作用に関して自然。 -/
lemma endomorphismModuleEvaluation_naturality (x y : Dᵒᵖ) :
    ((endomorphismModuleTensor A D E).obj ((endomorphismModuleHom A D E).obj M)).map x y ≫
        homPostcompose _ (endomorphismModuleEvaluationComponent A D E M y.unop) =
      M.map x y ≫ homPrecompose (endomorphismModuleEvaluationComponent A D E M x.unop) _ := by
  apply BalancedTensor.homMap_post_pre_eq A (EndomorphismObject E)
    ((endomorphismModuleHom A D E).obj M) ((endomorphismModuleAction A D E).leftAt x.unop)
  intro p f b r s a n ha hn m t
  cases b
  subst a
  change (moduleHom A D E M).X r at m
  change (E.obj x).X s at t
  change (endomorphismModuleEvaluationComponent A D E M y.unop).f n
    (moduleAction A ((endomorphismModuleTensor A D E).obj ((endomorphismModuleHom A D E).obj M))
      (x := x) (y := y) f (BalancedTensor.element A _ _ _ .point m t rfl) hn) = _
  have h := congrArg (fun z => (endomorphismModuleEvaluationComponent A D E M y.unop).f n z)
    (endomorphismModuleTensor_action_element A D E ((endomorphismModuleHom A D E).obj M)
      x y f m t hn)
  refine h.trans ?_
  simp only [Units.smul_def, map_zsmul]
  change (p * r).negOnePow • (endomorphismModuleEvaluationComponent A D E M y.unop).f n
      (BalancedTensor.element A _ _ _ .point m (moduleAction A E f t (by omega)) (by omega)) = _
  have he := endomorphismModuleEvaluation_element A D E M y.unop m
    (moduleAction A E (x := x) (y := y) f t (by omega : s + p = p + s)) (by omega : r + (p + s) = n)
  have hi := endomorphismModuleEvaluation_element A D E M x.unop m t rfl
  exact ((congrArg (fun z => (p * r).negOnePow • z) he).trans
    (endomorphismModuleEvaluation_action A D E M x y f m t hn)).trans
      (congrArg (fun z => moduleAction A M (x := x) (y := y) f z hn) hi.symm)

/-- 再構成tensorからMへの実際の閉零dg加群射。 -/
def endomorphismModuleEvaluation :
    ForgetEnrichment.of (Complex A)
      ((endomorphismModuleTensor A D E).obj ((endomorphismModuleHom A D E).obj M)) ⟶
        ForgetEnrichment.of (Complex A) M :=
  moduleMorphismMk A D (fun d => endomorphismModuleEvaluationComponent A D E M d.unop)
    (endomorphismModuleEvaluation_naturality A D E M)

@[simp]
lemma endomorphismModuleEvaluation_eval (d : D) :
    (moduleEvaluation A D d).map (endomorphismModuleEvaluation A D E M) =
      endomorphismModuleEvaluationComponent A D E M d :=
  moduleMorphismMk_eval A D _ _ d

end SerrePositivity.DifferentialGraded
