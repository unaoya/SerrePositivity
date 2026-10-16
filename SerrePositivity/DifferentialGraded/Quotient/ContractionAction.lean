module
public import SerrePositivity.DifferentialGraded.Quotient.ContractionCochain
public import SerrePositivity.DifferentialGraded.Quotient.ErasureHeadCochainNaturality
public import SerrePositivity.DifferentialGraded.Complexes.TensorZeroCochain

/-! # 指定収縮のHomへの作用と、その微分のε消去表示 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]
  {S : Set D} {E : Type w} [DGCategory A E]

/-- 像対象のHomへ、選択した収縮cochainを先頭から作用させる。 -/
def contractionAction (C : ContractedFunctor A D S E) (b : S) (y : E) :
    Cochain (epsilonComplex A ⊗ homObject A E (C.toDGFunctor.obj b.val) y)
      (homObject A E (C.toDGFunctor.obj b.val) y) 0 :=
  ((tensorRightHom (homObject A E (C.toDGFunctor.obj b.val) y) (epsilonComplex A)
    (homObject A E (C.toDGFunctor.obj b.val) (C.toDGFunctor.obj b.val))).f 0
      (contractionCochain A C b)).comp
    (Cochain.ofHom (eComp (Complex A) (C.toDGFunctor.obj b.val) (C.toDGFunctor.obj b.val) y))
      (zero_add 0)

lemma contractionAction_differential (C : ContractedFunctor A D S E) (b : S) (y : E) :
    δ 0 1 (contractionAction A C b y) =
      eraseHead A (homObject A E (C.toDGFunctor.obj b.val) y) := by
  have hu : (eId (Complex A) (C.toDGFunctor.obj b.val) ▷
      homObject A E (C.toDGFunctor.obj b.val) y) ≫
      eComp (Complex A) (C.toDGFunctor.obj b.val) (C.toDGFunctor.obj b.val) y =
    (λ_ (homObject A E (C.toDGFunctor.obj b.val) y)).hom := by
    apply (cancel_epi (λ_ (homObject A E (C.toDGFunctor.obj b.val) y)).inv).1
    rw [e_id_comp, Iso.inv_hom_id]
  rw [contractionAction, δ_comp_ofHom,
    homComplexMap_differential (tensorRightHom _ _ _) 0 1,
    contractionCochain_differential, tensorRightHom_cochain_comp, tensorRightHom_ofHom,
    Cochain.comp_assoc_of_third_is_zero_cochain, ← Cochain.ofHom_comp, hu]
  rfl

lemma contractionAction_evaluate (C : ContractedFunctor A D S E) (b : S) (y : E)
    (P : Complex A) (f : Cochain P (homObject A E (C.toDGFunctor.obj b.val) y) 0) :
    (tensorZeroCochain (contractionCochain A C b) f).comp
      (Cochain.ofHom (eComp (Complex A) (C.toDGFunctor.obj b.val) (C.toDGFunctor.obj b.val) y))
        (zero_add 0) =
    ((tensorLeftHom (epsilonComplex A) P (homObject A E (C.toDGFunctor.obj b.val) y)).f 0 f).comp
      (contractionAction A C b y) (zero_add 0) := by
  have h := tensorCochain_interchange (epsilonComplex A)
    (homObject A E (C.toDGFunctor.obj b.val) (C.toDGFunctor.obj b.val))
    P (homObject A E (C.toDGFunctor.obj b.val) y) 0 0 0 (zero_add 0) (zero_add 0)
    (contractionCochain A C b) f
  simp only [mul_zero, Int.negOnePow_zero, one_smul] at h
  rw [tensorZeroCochain, h, Cochain.comp_assoc_of_third_is_zero_cochain]
  rfl

lemma contractionAction_evaluation_differential (C : ContractedFunctor A D S E) (b : S) (y : E)
    (P : Complex A) (f : Cochain P (homObject A E (C.toDGFunctor.obj b.val) y) 0) :
    δ 0 1 ((tensorZeroCochain (contractionCochain A C b) f).comp
      (Cochain.ofHom (eComp (Complex A) (C.toDGFunctor.obj b.val) (C.toDGFunctor.obj b.val) y))
        (zero_add 0)) =
    (eraseHead A P).comp f (add_zero 1) +
    ((tensorLeftHom (epsilonComplex A) P (homObject A E (C.toDGFunctor.obj b.val) y)).f 1
      (δ 0 1 f)).comp (contractionAction A C b y) (add_zero 1) := by
  rw [contractionAction_evaluate,
    δ_comp _ _ (zero_add 0) 1 1 1 (zero_add 1) (zero_add 1) (zero_add 1),
    contractionAction_differential,
    homComplexMap_differential (tensorLeftHom _ _ _) 0 1,
    eraseHead_cochain_zero]
  simp only [Int.negOnePow_zero, one_smul]

end SerrePositivity.DifferentialGraded.DGQuotient
