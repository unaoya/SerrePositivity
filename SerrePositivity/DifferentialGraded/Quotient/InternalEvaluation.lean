module
public import SerrePositivity.DifferentialGraded.Quotient.PathEvaluation
public import SerrePositivity.DifferentialGraded.Quotient.PathCochainDesc

/-! # 指定収縮付きdg関手による全path直和の評価cochain -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D] [Small.{u} D]
  {S : Set D} {E : Type w} [DGCategory A E]

/-- 各有限pathの評価を貼り合わせた次数0 cochain。微分との整合性は別に証明する。 -/
def internalEvaluation (C : ContractedFunctor A D S E) (x y : D) :
    Cochain (internalHom A D S x y)
      (homObject A E (C.toDGFunctor.obj x) (C.toDGFunctor.obj y)) 0 :=
  pathCochainDesc A D S x y _ 0 (fun w => pathEvaluation A C w x y)

lemma internalEvaluation_precomp (C : ContractedFunctor A D S E) (x y : D) (w : Word S) :
    (Cochain.ofHom (ι A D S x y w)).comp (internalEvaluation A C x y) (zero_add 0) =
      pathEvaluation A C w x y := pathCochainDesc_precomp A D S x y _ 0 _ w

lemma internalEvaluation_original (C : ContractedFunctor A D S E) (x y : D) :
    (Cochain.ofHom (originalHom A D S x y)).comp (internalEvaluation A C x y) (zero_add 0) =
      Cochain.ofHom (C.toDGFunctor.map x y) := internalEvaluation_precomp A C x y []

lemma internalEvaluation_epsilon (C : ContractedFunctor A D S E) (b : S) :
    (Cochain.ofHom (epsilon A D S b)).comp (internalEvaluation A C b.val b.val) (zero_add 0) =
      contractionCochain A C b := by
  rw [epsilon, Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain,
    internalEvaluation_precomp]
  apply (Cochain.fromSingleEquiv (add_zero (-1))).injective
  apply (moduleElementEquiv A _).injective
  change ((Cochain.ofHom (epsilonTerm A D b)).comp (pathEvaluation A C [b] b.val b.val)
      (zero_add 0)).v (-1) (-1) (add_zero (-1))
      ((singleObjXSelf (.up ℤ) (-1) (𝟙_ (ModuleCat.{u} A))).inv (1 : A)) =
    (contractionCochain A C b).v (-1) (-1) (add_zero (-1))
      ((singleObjXSelf (.up ℤ) (-1) (𝟙_ (ModuleCat.{u} A))).inv (1 : A))
  rw [cochain_ofHom_comp_apply, pathEvaluation_epsilonTerm, contractionCochain_generator]

end SerrePositivity.DifferentialGraded.DGQuotient
