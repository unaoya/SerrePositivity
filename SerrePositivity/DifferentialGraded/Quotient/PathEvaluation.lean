module
public import SerrePositivity.DifferentialGraded.Quotient.ContractionCochain
public import SerrePositivity.DifferentialGraded.Complexes.TensorZeroCochain

/-! # 指定収縮付きdg関手による有限pathの評価 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]
  {S : Set D} {E : Type w} [DGCategory A E]

/-- 各HomをFで写し、各εを選択した収縮元へ送って豊穣合成する次数0 cochain。 -/
def pathEvaluation (C : ContractedFunctor A D S E) : ∀ (w : Word S) (x y : D),
    Cochain (term A D w x y) (homObject A E (C.toDGFunctor.obj x) (C.toDGFunctor.obj y)) 0
  | [], x, y => Cochain.ofHom (C.toDGFunctor.map x y)
  | b :: w, x, y =>
    (tensorZeroCochain (Cochain.ofHom (C.toDGFunctor.map x b.val))
      ((tensorZeroCochain (contractionCochain A C b) (pathEvaluation C w b.val y)).comp
        (Cochain.ofHom (eComp (Complex A) (C.toDGFunctor.obj b.val)
          (C.toDGFunctor.obj b.val) (C.toDGFunctor.obj y))) (zero_add 0))).comp
      (Cochain.ofHom (eComp (Complex A) (C.toDGFunctor.obj x)
        (C.toDGFunctor.obj b.val) (C.toDGFunctor.obj y))) (zero_add 0)

@[simp] lemma pathEvaluation_nil (C : ContractedFunctor A D S E) (x y : D) :
    pathEvaluation A C [] x y = Cochain.ofHom (C.toDGFunctor.map x y) := rfl

/-- 前方Hom・標準ε・後方pathの純tensor評価。追加符号は生じない。 -/
lemma pathEvaluation_cons_generator (C : ContractedFunctor A D S E) (b : S) (w : Word S)
    (x y : D) (p q n : ℤ) (hn : p + ((-1) + q) = n)
    (f : (homObject A D x b.val).X p) (t : (term A D w b.val y).X q) :
    (pathEvaluation A C (b :: w) x y).v n n (add_zero n)
      (ιTensorObj (homObject A D x b.val) (epsilonComplex A ⊗ term A D w b.val y)
        p ((-1) + q) n hn
        (f ⊗ₜ[A] ιTensorObj (epsilonComplex A) (term A D w b.val y) (-1) q ((-1) + q) rfl
          ((singleObjXSelf (.up ℤ) (-1) (𝟙_ (ModuleCat.{u} A))).inv (1 : A) ⊗ₜ[A] t))) =
    forward A ((C.toDGFunctor.map x b.val).f p f)
      (forward A (C.homotopy b) ((pathEvaluation A C w b.val y).v q q (add_zero q) t) rfl) hn := by
  change ((tensorZeroCochain (Cochain.ofHom (C.toDGFunctor.map x b.val))
      ((tensorZeroCochain (contractionCochain A C b) (pathEvaluation A C w b.val y)).comp
        (Cochain.ofHom (eComp (Complex A) (C.toDGFunctor.obj b.val)
          (C.toDGFunctor.obj b.val) (C.toDGFunctor.obj y))) (zero_add 0))).comp
      (Cochain.ofHom (eComp (Complex A) (C.toDGFunctor.obj x)
        (C.toDGFunctor.obj b.val) (C.toDGFunctor.obj y))) (zero_add 0)).v n n (add_zero n)
      (ιTensorObj (homObject A D x b.val) (epsilonComplex A ⊗ term A D w b.val y)
        p ((-1) + q) n hn
        (f ⊗ₜ[A] ιTensorObj (epsilonComplex A) (term A D w b.val y) (-1) q ((-1) + q) rfl
          ((singleObjXSelf (.up ℤ) (-1) (𝟙_ (ModuleCat.{u} A))).inv (1 : A) ⊗ₜ[A] t))) = _
  rw [cochain_comp_ofHom_apply, tensorZeroCochain_apply,
    cochain_comp_ofHom_apply, tensorZeroCochain_apply, contractionCochain_generator]
  rfl

/-- 両側の単位を持つ単一ε pathは、選択した収縮元そのものへ評価される。 -/
lemma pathEvaluation_epsilonTerm (C : ContractedFunctor A D S E) (b : S) :
    (pathEvaluation A C [b] b.val b.val).v (-1) (-1) (add_zero (-1))
      ((epsilonTerm A D b).f (-1)
        ((singleObjXSelf (.up ℤ) (-1) (𝟙_ (ModuleCat.{u} A))).inv (1 : A))) = C.homotopy b := by
  have he := congrArg (fun v : (term A D [b] b.val b.val).X (-1) =>
    (pathEvaluation A C [b] b.val b.val).v (-1) (-1) (add_zero (-1)) v)
    (epsilonTerm_generator A D b)
  have h := pathEvaluation_cons_generator A C b [] b.val b.val 0 0 (-1) (by omega)
    (unitElement A b.val).val (unitElement A b.val).val
  simp only [term_nil, pathEvaluation_nil, Cochain.ofHom_v, DGFunctor.map_unitElement,
    unit_forward, forward_unit] at h
  exact he.trans h

end SerrePositivity.DifferentialGraded.DGQuotient
