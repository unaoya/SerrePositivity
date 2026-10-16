module
public import SerrePositivity.DifferentialGraded.Quotient.EvaluationErasure
public import SerrePositivity.DifferentialGraded.Complexes.PerturbationMap

/-! # 指定収縮付きdg関手の最終商Hom上の評価chain map -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D] [Small.{u} D]
  {S : Set D} {E : Type w} [DGCategory A E]

/-- 指定収縮を使う評価は、最終Hom微分についての実際のchain mapとなる。 -/
def quotientEvaluation (C : ContractedFunctor A D S E) (x y : D) :
    quotientHom A D S x y ⟶ homObject A E (C.toDGFunctor.obj x) (C.toDGFunctor.obj y) :=
  perturbSourceMap (internalHom A D S x y)
    (homObject A E (C.toDGFunctor.obj x) (C.toDGFunctor.obj y))
    (erasure A D S x y) (erasure_closed A D S x y) (erasure_square_zero A D S x y)
    (internalEvaluation A C x y) (internalEvaluation_differential A C x y)

lemma quotientEvaluation_f (C : ContractedFunctor A D S E) (x y : D) (i : ℤ) :
    (quotientEvaluation A C x y).f i = (internalEvaluation A C x y).v i i (add_zero i) := rfl

lemma quotientEvaluation_original (C : ContractedFunctor A D S E) (x y : D) :
    originalHomInclusion A D S x y ≫ quotientEvaluation A C x y = C.toDGFunctor.map x y := by
  apply HomologicalComplex.Hom.ext
  funext i
  rw [HomologicalComplex.comp_f, originalHomInclusion_f, quotientEvaluation_f]
  have h := congrArg (fun f : Cochain (homObject A D x y)
      (homObject A E (C.toDGFunctor.obj x) (C.toDGFunctor.obj y)) 0 =>
    f.v i i (add_zero i)) (internalEvaluation_original A C x y)
  simpa only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v] using h

lemma quotientEvaluation_epsilon (C : ContractedFunctor A D S E) (b : S) :
    (quotientEvaluation A C b.val b.val).f (-1) (epsilonElement A D S b) = C.homotopy b := by
  have h := congrArg (fun f : Cochain (epsilonComplex A)
      (homObject A E (C.toDGFunctor.obj b.val) (C.toDGFunctor.obj b.val)) 0 =>
    f.v (-1) (-1) (add_zero (-1))
      ((singleObjXSelf (.up ℤ) (-1) (𝟙_ (ModuleCat.{u} A))).inv (1 : A)))
    (internalEvaluation_epsilon A C b)
  rw [cochain_ofHom_comp_apply, contractionCochain_generator] at h
  exact h

lemma quotientEvaluation_path (C : ContractedFunctor A D S E) (w : Word S) (x y : D) (i : ℤ) :
    (ι A D S x y w).f i ≫ (quotientEvaluation A C x y).f i =
      (pathEvaluation A C w x y).v i i (add_zero i) := by
  rw [quotientEvaluation_f]
  have h := congrArg (fun f : Cochain (term A D w x y)
      (homObject A E (C.toDGFunctor.obj x) (C.toDGFunctor.obj y)) 0 =>
    f.v i i (add_zero i)) (internalEvaluation_precomp A C x y w)
  simpa only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v] using h

lemma quotientEvaluation_unit (C : ContractedFunctor A D S E) (x : D) :
    quotientIdentity A D S x ≫ quotientEvaluation A C x x =
      eId (Complex A) (C.toDGFunctor.obj x) := by
  rw [quotientIdentity, Category.assoc, quotientEvaluation_original, C.toDGFunctor.map_id]

end SerrePositivity.DifferentialGraded.DGQuotient
