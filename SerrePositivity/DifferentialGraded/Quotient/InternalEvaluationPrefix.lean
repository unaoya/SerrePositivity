module
public import SerrePositivity.DifferentialGraded.Quotient.InternalEvaluation
public import SerrePositivity.DifferentialGraded.Quotient.EvaluationPrefix
public import SerrePositivity.DifferentialGraded.Quotient.PathPrefix

/-! # 全path直和への前方Hom・ε追加と評価の整合性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D] [Small.{u} D]
  {S : Set D} {E : Type w} [DGCategory A E]

lemma internalEvaluation_prefixPath (C : ContractedFunctor A D S E) (b : S) (x y : D) :
    (Cochain.ofHom (prefixPath A D b x y)).comp (internalEvaluation A C x y) (zero_add 0) =
    ((tensorLeftHom (homObject A D x b.val)
      (epsilonComplex A ⊗ internalHom A D S b.val y)
      (epsilonComplex A ⊗ homObject A E (C.toDGFunctor.obj b.val) (C.toDGFunctor.obj y))).f 0
      ((tensorLeftHom (epsilonComplex A) (internalHom A D S b.val y)
        (homObject A E (C.toDGFunctor.obj b.val) (C.toDGFunctor.obj y))).f 0
          (internalEvaluation A C b.val y))).comp
      (evaluationPrefixAction A C b x y) (zero_add 0) := by
  apply prefixPathCochain_ext A D b x y 0
  intro w
  have ht :
      (Cochain.ofHom ((homObject A D x b.val) ◁ ((epsilonComplex A) ◁ ι A D S b.val y w))).comp
        ((tensorLeftHom (homObject A D x b.val)
          (epsilonComplex A ⊗ internalHom A D S b.val y)
          (epsilonComplex A ⊗ homObject A E (C.toDGFunctor.obj b.val) (C.toDGFunctor.obj y))).f 0
          ((tensorLeftHom (epsilonComplex A) (internalHom A D S b.val y)
            (homObject A E (C.toDGFunctor.obj b.val) (C.toDGFunctor.obj y))).f 0
              (internalEvaluation A C b.val y))) (zero_add 0) =
      (tensorLeftHom (homObject A D x b.val) (epsilonComplex A ⊗ term A D w b.val y)
        (epsilonComplex A ⊗ homObject A E (C.toDGFunctor.obj b.val) (C.toDGFunctor.obj y))).f 0
        ((tensorLeftHom (epsilonComplex A) (term A D w b.val y)
          (homObject A E (C.toDGFunctor.obj b.val) (C.toDGFunctor.obj y))).f 0
            (pathEvaluation A C w b.val y)) := by
    rw [← tensorLeftHom_ofHom (homObject A D x b.val), ← tensorLeftHom_cochain_comp,
      ← tensorLeftHom_ofHom (epsilonComplex A), ← tensorLeftHom_cochain_comp,
      internalEvaluation_precomp]
  rw [← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.ofHom_comp,
    prefixPath_ι, internalEvaluation_precomp,
    ← Cochain.comp_assoc_of_first_is_zero_cochain, ht]
  exact pathEvaluation_cons_action A C b w x y

end SerrePositivity.DifferentialGraded.DGQuotient
