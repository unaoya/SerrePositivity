module
public import SerrePositivity.DifferentialGraded.Quotient.ContractedFunctor

/-! # 指定収縮元からεの評価cochainを構成する -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]
  {S : Set D} {E : Type w} [DGCategory A E]

/-- εを指定収縮元へ送る次数0 cochain。閉零chain mapではない。 -/
def contractionCochain (C : ContractedFunctor A D S E) (b : S) :
    Cochain (epsilonComplex A)
      (homObject A E (C.toDGFunctor.obj b.val) (C.toDGFunctor.obj b.val)) 0 :=
  Cochain.fromSingleMk (p := -1) (q := -1)
    (moduleElementMap A _ (C.homotopy b)) (add_zero (-1))

lemma contractionCochain_generator (C : ContractedFunctor A D S E) (b : S) :
    (contractionCochain A C b).v (-1) (-1) (add_zero (-1))
      ((singleObjXSelf (.up ℤ) (-1) (𝟙_ (ModuleCat.{u} A))).inv (1 : A)) = C.homotopy b := by
  rw [contractionCochain, Cochain.fromSingleMk_v]
  change (moduleElementMap A _ (C.homotopy b))
    (((singleObjXSelf (.up ℤ) (-1) (𝟙_ (ModuleCat.{u} A))).inv ≫
      (singleObjXSelf (.up ℤ) (-1) (𝟙_ (ModuleCat.{u} A))).hom) (1 : A)) = _
  rw [Iso.inv_hom_id]
  exact one_smul A (C.homotopy b)

/-- 収縮cochainの微分は、εを消して像対象の単位を挿入するcochain。 -/
lemma contractionCochain_differential (C : ContractedFunctor A D S E) (b : S) :
    δ 0 1 (contractionCochain A C b) =
    (eraseEpsilon A).comp (Cochain.ofHom (eId (Complex A) (C.toDGFunctor.obj b.val)))
      (add_zero 1) := by
  rw [contractionCochain, Cochain.δ_fromSingleMk _ _ 1 0 (by omega), eraseEpsilon,
    ← Cochain.fromSingleMk_postcomp]
  congr 1
  apply (moduleElementEquiv A _).injective
  change (homObject A E (C.toDGFunctor.obj b.val) (C.toDGFunctor.obj b.val)).d (-1) 0
    ((1 : A) • C.homotopy b) = (unitElement A (C.toDGFunctor.obj b.val)).val
  rw [one_smul]
  exact C.d_homotopy b

end SerrePositivity.DifferentialGraded.DGQuotient
