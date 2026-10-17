module
public import SerrePositivity.DifferentialGraded.Endomorphism.ModuleComparison
public import SerrePositivity.DifferentialGraded.Tensor.Homotopy

/-! # 再構成Hom・tensor関手の全Hom写像の計算

単位・余単位の自然性に用いる。閉零の式も全Hom写像から取り出す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (E : RightModule A D)

/-- 再構成Hom関手の全Hom写像をEnd(E)の一対象で評価する。 -/
lemma endomorphismModuleHom_map_π (M M' : RightModule A D) :
    (endomorphismModuleHom A D E).map M M' ≫
      moduleHomπ A (EndomorphismObject E) ((endomorphismModuleHom A D E).obj M)
        ((endomorphismModuleHom A D E).obj M') .point =
      (leftRepresentable A E).map M M' := by
  change (moduleHomEquiv A (EndomorphismObject E) _ _ _).symm
    (largeEndomorphismHomParam A (RightModule A D) E M M') ≫ _ = _
  exact (moduleHomEquiv_symm_π A (EndomorphismObject E) _
    (endomorphismHomRight A (RightModule A D) E M)
    (endomorphismHomRight A (RightModule A D) E M')
    (largeEndomorphismHomParam A (RightModule A D) E M M') .point).trans
      (endomorphismYonedaApp A (RightModule A D) E M M')

/-- Hom関手の斉次作用はEndにおける前合成と逆向きの後合成。 -/
lemma endomorphismModuleHom_map_element (M M' : RightModule A D) {p r n : ℤ}
    (f : (moduleHom A D M M').X p) (m : (moduleHom A D E M).X r) (hn : r + p = n) :
    ((moduleHomπ A (EndomorphismObject E) ((endomorphismModuleHom A D E).obj M)
        ((endomorphismModuleHom A D E).obj M') .point).f p
      (((endomorphismModuleHom A D E).map M M').f p f)).v r n hn m =
    (p * r).negOnePow • forward A (D := RightModule A D) (x := E) (y := M) (z := M') m f hn := by
  have h := congrArg (fun k => (k.f p f).v r n hn m)
    (endomorphismModuleHom_map_π A D E M M')
  exact h.trans (leftRepresentable_action A E M M' f m hn)

/-- 再構成tensor関手のD成分は既存balanced tensorの右Hom写像。 -/
lemma endomorphismModuleTensor_map_π (N N' : RightModule A (EndomorphismObject E)) (d : D) :
    (endomorphismModuleTensor A D E).map N N' ≫
      moduleHomπ A D ((endomorphismModuleTensor A D E).obj N)
        ((endomorphismModuleTensor A D E).obj N') d =
    BalancedTensor.rightHomMap A (EndomorphismObject E) N N'
      ((endomorphismModuleAction A D E).leftAt d) := by
  have h := BimoduleTensor.compose_leftMap_π A D (EndomorphismObject E)
    (RightModule A (EndomorphismObject E)) (endomorphismModuleAction A D E)
    (DGFunctor.id (RightModule A (EndomorphismObject E))) N N' d
  change (endomorphismModuleTensor A D E).map N N' ≫
      moduleHomπ A D ((endomorphismModuleTensor A D E).obj N)
        ((endomorphismModuleTensor A D E).obj N') d =
    𝟙 _ ≫ BalancedTensor.rightHomMap A (EndomorphismObject E) N N'
      ((endomorphismModuleAction A D E).leftAt d) at h
  exact h.trans (Category.id_comp _)

/-- 再構成tensorの全Hom写像の生成元公式。 -/
lemma endomorphismModuleTensor_map_element (N N' : RightModule A (EndomorphismObject E))
    (d : D) {p r s a l n : ℤ} (f : (moduleHom A (EndomorphismObject E) N N').X p)
    (m : (N.obj (op (.point : EndomorphismObject E))).X r) (t : (E.obj (op d)).X s)
    (ha : r + s = a) (hl : p + r = l) (hn : a + p = n) :
    ((moduleHomπ A D ((endomorphismModuleTensor A D E).obj N)
        ((endomorphismModuleTensor A D E).obj N') d).f p
      (((endomorphismModuleTensor A D E).map N N').f p f)).v a n hn
        (BalancedTensor.element A (EndomorphismObject E) N
          ((endomorphismModuleAction A D E).leftAt d) .point m t ha) =
    BalancedTensor.element A (EndomorphismObject E) N'
      ((endomorphismModuleAction A D E).leftAt d) .point
        (((moduleHomπ A (EndomorphismObject E) N N' .point).f p f).v r l (by omega) m) t
        (by omega) := by
  have h := congrArg (fun k => (k.f p f).v a n hn
    (BalancedTensor.element A (EndomorphismObject E) N
      ((endomorphismModuleAction A D E).leftAt d) .point m t ha))
    (endomorphismModuleTensor_map_π A D E N N' d)
  exact h.trans (BalancedTensor.rightHomMap_element_of_sum A (EndomorphismObject E)
    ((endomorphismModuleAction A D E).leftAt d) f .point m t ha hl hn)

/-- 再構成tensorの閉零射は、D成分ごとに既存balanced tensorの閉零射となる。 -/
lemma endomorphismModuleTensor_map_eval {N N' : ModuleCategory A (EndomorphismObject E)}
    (f : N ⟶ N') (d : D) :
    (moduleEvaluation A D d).map ((endomorphismModuleTensor A D E).onClosed.map f) =
      BalancedTensor.rightTensorMap A (EndomorphismObject E)
        ((endomorphismModuleAction A D E).leftAt d) f := by
  apply Cochain.ofHom_injective
  rw [moduleEvaluation_cochain]
  change (moduleHomπ A D _ _ d).f 0
    (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) f ≫
      (endomorphismModuleTensor A D E).map _ _)).val = _
  rw [cycleFromUnit_postcomp]
  have h := congrArg (fun k => k.f 0 (cycleFromUnit _
    (ForgetEnrichment.homTo (Complex A) f)).val)
      (endomorphismModuleTensor_map_π A D E
        (ForgetEnrichment.to (Complex A) N) (ForgetEnrichment.to (Complex A) N') d)
  exact h.trans (BalancedTensor.rightHomMap_closedElement A (EndomorphismObject E)
    ((endomorphismModuleAction A D E).leftAt d) f)

/-- tensor関手の閉零射は生成元のEnd加群成分だけを動かす。 -/
lemma endomorphismModuleTensor_map_eval_element {N N' : ModuleCategory A (EndomorphismObject E)}
    (f : N ⟶ N') (d : D) {r s n : ℤ}
    (m : ((ForgetEnrichment.to (Complex A) N).obj (op (.point : EndomorphismObject E))).X r)
    (t : (E.obj (op d)).X s) (hn : r + s = n) :
    ((moduleEvaluation A D d).map ((endomorphismModuleTensor A D E).onClosed.map f)).f n
      (BalancedTensor.element A (EndomorphismObject E) (ForgetEnrichment.to (Complex A) N)
        ((endomorphismModuleAction A D E).leftAt d) .point m t hn) =
    BalancedTensor.element A (EndomorphismObject E) (ForgetEnrichment.to (Complex A) N')
      ((endomorphismModuleAction A D E).leftAt d) .point
        (((moduleEvaluation A (EndomorphismObject E) .point).map f).f r m) t hn := by
  have h := congrArg (fun k => k.f n
    (BalancedTensor.element A (EndomorphismObject E) (ForgetEnrichment.to (Complex A) N)
      ((endomorphismModuleAction A D E).leftAt d) .point m t hn))
        (endomorphismModuleTensor_map_eval A D E f d)
  exact h.trans (BalancedTensor.rightTensorMap_element A (EndomorphismObject E)
    ((endomorphismModuleAction A D E).leftAt d) f .point m t hn)

/-- Hom関手の閉零射を全Hom要素とEの元で評価すると、元の加群射の後合成になる。 -/
lemma endomorphismModuleHom_map_eval_apply (M M' : RightModule A D)
    (f : ForgetEnrichment.of (Complex A) M ⟶ ForgetEnrichment.of (Complex A) M') (d : D)
    {r s n : ℤ} (m : (moduleHom A D E M).X r) (t : (E.obj (op d)).X s) (hn : s + r = n) :
    ((moduleHomπ A D E M' d).f r
      (((moduleEvaluation A (EndomorphismObject E) .point).map
        ((endomorphismModuleHom A D E).onClosed.map f)).f r m)).v s n hn t =
    ((moduleEvaluation A D d).map f).f n (((moduleHomπ A D E M d).f r m).v s n hn t) := by
  have hc := moduleEvaluation_cochain A (EndomorphismObject E) .point
    ((endomorphismModuleHom A D E).onClosed.map f)
  change Cochain.ofHom ((moduleEvaluation A (EndomorphismObject E) .point).map
      ((endomorphismModuleHom A D E).onClosed.map f)) =
    (moduleHomπ A (EndomorphismObject E) ((endomorphismModuleHom A D E).obj M)
      ((endomorphismModuleHom A D E).obj M') .point).f 0
        (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) f ≫
          (endomorphismModuleHom A D E).map M M')).val at hc
  rw [cycleFromUnit_postcomp] at hc
  have he := congrArg (fun c => c.v r r (add_zero r) m) hc
  rw [Cochain.ofHom_v] at he
  have hm := endomorphismModuleHom_map_element A D E M M'
    (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) f)).val m (add_zero r)
  simp only [zero_mul, Int.negOnePow_zero, one_smul] at hm
  have hv := congrArg (fun z => ((moduleHomπ A D E M' d).f r z).v s n hn t) (he.trans hm)
  rw [moduleHomForward_π, Cochain.units_smul_v,
    Cochain.comp_v _ _ _ s n n hn (add_zero n)] at hv
  simp only [mul_zero, Int.negOnePow_zero, one_smul] at hv
  have hf := congrArg (fun c => c.v n n (add_zero n)
    (((moduleHomπ A D E M d).f r m).v s n hn t)) (moduleEvaluation_cochain A D d f)
  rw [Cochain.ofHom_v] at hf
  exact hv.trans hf.symm

end SerrePositivity.DifferentialGraded
