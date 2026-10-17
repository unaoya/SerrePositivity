module
public import SerrePositivity.DifferentialGraded.Endomorphism.ModuleInsertion
public import SerrePositivity.DifferentialGraded.Endomorphism.ModuleFunctorMaps
public import Mathlib.CategoryTheory.Adjunction.Basic

/-! # 指定dg加群Eに対するtensor–Hom再構成随伴

全加群dg圏の対象型のsmall性を仮定せず、閉零加群圏で単位・余単位を組み立てる。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (E : RightModule A D)

/-- 再構成随伴の単位。挿入射はEnd(E)加群変数にも自然。 -/
def endomorphismModuleUnit :
    𝟭 (ModuleCategory A (EndomorphismObject E)) ⟶
      (endomorphismModuleTensor A D E).onClosed ⋙ (endomorphismModuleHom A D E).onClosed where
  app N := endomorphismModuleInsertion A D E (ForgetEnrichment.to (Complex A) N)
  naturality {N N'} f := by
    apply moduleMorphism_ext
    intro b
    cases b
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
      endomorphismModuleInsertion_eval, endomorphismModuleInsertion_eval]
    apply HomologicalComplex.hom_ext
    intro r
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    apply moduleHomElement_ext A D
    intro d
    apply Cochain.ext
    intro s n hn
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro t
    change ((moduleHomπ A D E
        ((endomorphismModuleTensor A D E).obj (ForgetEnrichment.to (Complex A) N')) d).f r
      ((endomorphismModuleInsertionHom A D E (ForgetEnrichment.to (Complex A) N')).f r
        (((moduleEvaluation A (EndomorphismObject E) .point).map f).f r m))).v s n hn t = _
    have hi := endomorphismModuleInsertionHom_element A D E
      (ForgetEnrichment.to (Complex A) N) d m t hn
    have hi' := endomorphismModuleInsertionHom_element A D E
      (ForgetEnrichment.to (Complex A) N') d
        (((moduleEvaluation A (EndomorphismObject E) .point).map f).f r m) t hn
    have ht := endomorphismModuleTensor_map_eval_element A D E f d m t
      (by omega : r + s = n)
    have hr := endomorphismModuleHom_map_eval_apply A D E
      ((endomorphismModuleTensor A D E).obj (ForgetEnrichment.to (Complex A) N))
      ((endomorphismModuleTensor A D E).obj (ForgetEnrichment.to (Complex A) N'))
      ((endomorphismModuleTensor A D E).onClosed.map f) d
      ((endomorphismModuleInsertionHom A D E (ForgetEnrichment.to (Complex A) N)).f r m) t hn
    exact hi'.trans (ht.symm.trans ((congrArg (fun z =>
      ((moduleEvaluation A D d).map ((endomorphismModuleTensor A D E).onClosed.map f)).f n z)
        hi.symm).trans hr.symm))

/-- 再構成随伴の余単位。評価射はD加群変数にも自然。 -/
def endomorphismModuleCounit :
    (endomorphismModuleHom A D E).onClosed ⋙ (endomorphismModuleTensor A D E).onClosed ⟶
      𝟭 (ModuleCategory A D) where
  app M := endomorphismModuleEvaluation A D E (ForgetEnrichment.to (Complex A) M)
  naturality {M M'} f := by
    apply moduleMorphism_ext
    intro d
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
      endomorphismModuleEvaluation_eval, endomorphismModuleEvaluation_eval]
    apply Cochain.ofHom_injective
    apply BalancedTensor.cochain_zero_element_ext A (EndomorphismObject E)
      ((endomorphismModuleHom A D E).obj (ForgetEnrichment.to (Complex A) M))
      ((endomorphismModuleAction A D E).leftAt d)
    intro b r s n hn m t
    cases b
    simp only [Cochain.ofHom_v]
    change (endomorphismModuleEvaluationComponent A D E (ForgetEnrichment.to (Complex A) M') d).f n
      (((moduleEvaluation A D d).map ((endomorphismModuleTensor A D E).onClosed.map
        ((endomorphismModuleHom A D E).onClosed.map f))).f n
          (BalancedTensor.element A _ _ _ .point m t hn)) = _
    have ht := endomorphismModuleTensor_map_eval_element A D E
      ((endomorphismModuleHom A D E).onClosed.map f) d m t hn
    have he' := endomorphismModuleEvaluation_element A D E (ForgetEnrichment.to (Complex A) M') d
      (((moduleEvaluation A (EndomorphismObject E) .point).map
        ((endomorphismModuleHom A D E).onClosed.map f)).f r m) t hn
    have he := endomorphismModuleEvaluation_element A D E
      (ForgetEnrichment.to (Complex A) M) d m t hn
    have hr := endomorphismModuleHom_map_eval_apply A D E
      (ForgetEnrichment.to (Complex A) M) (ForgetEnrichment.to (Complex A) M') f d m t
        (by omega : s + r = n)
    exact (congrArg (fun z =>
      (endomorphismModuleEvaluationComponent A D E (ForgetEnrichment.to (Complex A) M') d).f n z)
        ht).trans (he'.trans (hr.trans (congrArg (fun z => ((moduleEvaluation A D d).map f).f n z)
          he.symm)))

/-- 再構成tensorに関する左三角恒等式。 -/
lemma endomorphismModule_left_triangle (N : ModuleCategory A (EndomorphismObject E)) :
    (endomorphismModuleTensor A D E).onClosed.map ((endomorphismModuleUnit A D E).app N) ≫
      (endomorphismModuleCounit A D E).app
        ((endomorphismModuleTensor A D E).onClosed.obj N) = 𝟙 _ := by
  apply moduleMorphism_ext
  intro d
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id]
  dsimp only [endomorphismModuleCounit]
  rw [endomorphismModuleEvaluation_eval]
  apply Cochain.ofHom_injective
  apply BalancedTensor.cochain_zero_element_ext A (EndomorphismObject E)
    (ForgetEnrichment.to (Complex A) N) ((endomorphismModuleAction A D E).leftAt d)
  intro b r s n hn m t
  cases b
  simp only [Cochain.ofHom_v]
  have ht := endomorphismModuleTensor_map_eval_element A D E
    ((endomorphismModuleUnit A D E).app N) d m t hn
  have hu := endomorphismModuleInsertion_eval A D E (ForgetEnrichment.to (Complex A) N) .point
  have he := endomorphismModuleEvaluation_element A D E
    ((endomorphismModuleTensor A D E).obj (ForgetEnrichment.to (Complex A) N)) d
      ((endomorphismModuleInsertionHom A D E (ForgetEnrichment.to (Complex A) N)).f r m) t hn
  have hi := endomorphismModuleInsertionHom_element A D E (ForgetEnrichment.to (Complex A) N)
    d m t (by omega : s + r = n)
  change (endomorphismModuleEvaluationComponent A D E
    ((endomorphismModuleTensor A D E).obj (ForgetEnrichment.to (Complex A) N)) d).f n
      (((moduleEvaluation A D d).map ((endomorphismModuleTensor A D E).onClosed.map
        ((endomorphismModuleUnit A D E).app N))).f n
          (BalancedTensor.element A (EndomorphismObject E) (ForgetEnrichment.to (Complex A) N)
            ((endomorphismModuleAction A D E).leftAt d) .point m t hn)) = _
  have ht' := congrArg (fun z => (endomorphismModuleEvaluationComponent A D E
    ((endomorphismModuleTensor A D E).obj (ForgetEnrichment.to (Complex A) N)) d).f n z) ht
  dsimp only [endomorphismModuleUnit] at ht'
  rw [hu] at ht'
  exact ht'.trans (he.trans hi)

/-- 再構成Homに関する右三角恒等式。 -/
lemma endomorphismModule_right_triangle (M : ModuleCategory A D) :
    (endomorphismModuleUnit A D E).app ((endomorphismModuleHom A D E).onClosed.obj M) ≫
      (endomorphismModuleHom A D E).onClosed.map
        ((endomorphismModuleCounit A D E).app M) = 𝟙 _ := by
  apply moduleMorphism_ext
  intro b
  cases b
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id]
  apply HomologicalComplex.hom_ext
  intro r
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  apply moduleHomElement_ext A D
  intro d
  apply Cochain.ext
  intro s n hn
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro t
  have hu := endomorphismModuleInsertion_eval A D E
    ((endomorphismModuleHom A D E).obj (ForgetEnrichment.to (Complex A) M)) .point
  have hi := endomorphismModuleInsertionHom_element A D E
    ((endomorphismModuleHom A D E).obj (ForgetEnrichment.to (Complex A) M)) d m t hn
  have he := endomorphismModuleEvaluation_element A D E (ForgetEnrichment.to (Complex A) M)
    d m t (by omega : r + s = n)
  have hr := endomorphismModuleHom_map_eval_apply A D E
    ((endomorphismModuleTensor A D E).obj
      ((endomorphismModuleHom A D E).obj (ForgetEnrichment.to (Complex A) M)))
    (ForgetEnrichment.to (Complex A) M) ((endomorphismModuleCounit A D E).app M) d
    ((endomorphismModuleInsertionHom A D E
      ((endomorphismModuleHom A D E).obj (ForgetEnrichment.to (Complex A) M))).f r m) t hn
  change ((moduleHomπ A D E (ForgetEnrichment.to (Complex A) M) d).f r
    (((moduleEvaluation A (EndomorphismObject E) .point).map
      ((endomorphismModuleHom A D E).onClosed.map ((endomorphismModuleCounit A D E).app M))).f r
        (((moduleEvaluation A (EndomorphismObject E) .point).map
          (endomorphismModuleInsertion A D E
            ((endomorphismModuleHom A D E).obj (ForgetEnrichment.to (Complex A) M)))).f r m))).v
              s n hn t = _
  rw [hu]
  have hc := endomorphismModuleEvaluation_eval A D E (ForgetEnrichment.to (Complex A) M) d
  dsimp only [endomorphismModuleCounit] at hr
  rw [hc] at hr
  exact hr.trans ((congrArg (fun z =>
    (endomorphismModuleEvaluationComponent A D E (ForgetEnrichment.to (Complex A) M) d).f n z)
      hi).trans he)

/-- 既存balanced tensorと全Hom endによる、指定dg加群Eの再構成随伴。 -/
def endomorphismModuleAdjunction :
    (endomorphismModuleTensor A D E).onClosed ⊣ (endomorphismModuleHom A D E).onClosed :=
  Adjunction.mkOfUnitCounit
    { unit := endomorphismModuleUnit A D E
      counit := endomorphismModuleCounit A D E
      left_triangle := by
        apply NatTrans.ext
        funext N
        simpa only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
          Functor.associator_hom_app, Category.id_comp, Category.comp_id,
          Functor.comp_obj, Functor.id_obj, NatTrans.id] using
            endomorphismModule_left_triangle A D E N
      right_triangle := by
        apply NatTrans.ext
        funext M
        simpa only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
          Functor.associator_inv_app, Category.id_comp, Category.comp_id,
          Functor.comp_obj, Functor.id_obj, NatTrans.id] using
            endomorphismModule_right_triangle A D E M }

end SerrePositivity.DifferentialGraded
