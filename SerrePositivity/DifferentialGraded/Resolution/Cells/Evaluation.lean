module
public import SerrePositivity.DifferentialGraded.Resolution.Cells.EvaluationReplacement
public import SerrePositivity.DifferentialGraded.Complexes.PerturbationMap

/-! # 指定原始元付きdg関手の最終cell Hom上の評価chain map -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.DifferentialGraded.DGCellAttachment.Family.PrimitiveData
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D] {I : Type w} [Small.{u} I]
  {C : Family A D I} {E : Type z} [DGCategory A E] {F : DGFunctor A D E}
variable (P : PrimitiveData A D I C E F)

/-- 指定原始元を使う評価は、最終Hom微分についての実際のchain mapとなる。 -/
def attachedEvaluation (x y : D) :
    C.attachedHom A D I x y ⟶ homObject A E (F.obj x) (F.obj y) :=
  perturbSourceMap (C.internalHom A D I x y)
    (homObject A E (F.obj x) (F.obj y))
    (C.replacement A D I x y) (C.replacement_closed A D I x y) (C.replacement_square_zero A D I x y)
    (P.internalEvaluation x y) (P.internalEvaluation_differential x y)

lemma attachedEvaluation_f (x y : D) (i : ℤ) :
    (P.attachedEvaluation x y).f i = (P.internalEvaluation x y).v i i (add_zero i) := rfl

lemma attachedEvaluation_original (x y : D) :
    C.originalHomInclusion A D I x y ≫ P.attachedEvaluation x y = F.map x y := by
  apply HomologicalComplex.Hom.ext
  funext i
  rw [HomologicalComplex.comp_f, Family.originalHomInclusion_f, attachedEvaluation_f]
  have h := congrArg (fun f : Cochain (homObject A D x y)
      (homObject A E (F.obj x) (F.obj y)) 0 =>
    f.v i i (add_zero i)) (P.internalEvaluation_original x y)
  simpa only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v] using h

lemma attachedEvaluation_generator (i : I) :
    (P.attachedEvaluation (C.source i) (C.target i)).f (C.degree i)
      (C.generatorElement A D I i) = P.primitive i := by
  have h := congrArg (fun f : Cochain (C.generator A D I i)
      (homObject A E (F.obj (C.source i)) (F.obj (C.target i))) 0 =>
    f.v (C.degree i) (C.degree i) (add_zero _)
      ((singleObjXSelf (.up ℤ) (C.degree i) (𝟙_ (ModuleCat.{u} A))).inv (1 : A)))
    (P.internalEvaluation_generator i)
  rw [cochain_ofHom_comp_apply, cochain_generator] at h
  exact h

lemma attachedEvaluation_path (w : List I) (x y : D) (i : ℤ) :
    (C.inclusion A D I w x y).f i ≫ (P.attachedEvaluation x y).f i =
      (P.pathEvaluation w x y).v i i (add_zero i) := by
  rw [attachedEvaluation_f]
  have h := congrArg (fun f : Cochain (C.term A D I w x y)
      (homObject A E (F.obj x) (F.obj y)) 0 =>
    f.v i i (add_zero i)) (P.internalEvaluation_precomp x y w)
  simpa only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v] using h

lemma attachedEvaluation_unit (x : D) :
    C.attachedIdentity A D I x ≫ P.attachedEvaluation x x =
      eId (Complex A) (F.obj x) := by
  rw [Family.attachedIdentity, Category.assoc, attachedEvaluation_original, F.map_id]

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family.PrimitiveData
