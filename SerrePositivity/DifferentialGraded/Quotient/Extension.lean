module
public import SerrePositivity.DifferentialGraded.Quotient.EvaluationComposition

/-! # 指定収縮付きdg関手の商への延長と制限との一方の往復 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D] [Small.{u} D]
  {S : Set D} {E : Type w} [DGCategory A E]

/-- 各εを指定収縮へ送る、主豊穣モデル上の実際のdg関手。 -/
def extension (C : ContractedFunctor A D S E) : DGFunctor A (QuotientObject D S) E where
  obj x := C.toDGFunctor.obj x.val
  map x y := quotientEvaluation A C x.val y.val
  map_id x := quotientEvaluation_unit A C x.val
  map_comp x y z := quotientEvaluation_composition A C x.val y.val z.val

lemma inclusion_comp_extension (C : ContractedFunctor A D S E) :
    (inclusion A D S).comp (extension A C) = C.toDGFunctor := by
  apply EnrichedFunctor.ext (Complex A)
    (F := (inclusion A D S).comp (extension A C)) (G := C.toDGFunctor) (fun _ => rfl)
  intro x y
  change (originalHomInclusion A D S x y ≫ quotientEvaluation A C x y) ≫ eqToHom (by rfl) = _
  rw [eqToHom_refl, Category.comp_id, quotientEvaluation_original]

lemma restrict_extension_homotopy (C : ContractedFunctor A D S E) (b : S) :
    (restrictContractedFunctor A D S (extension A C)).homotopy b = C.homotopy b :=
  quotientEvaluation_epsilon A C b

omit [Small.{u} D] in
lemma ContractedFunctor.ext {C C' : ContractedFunctor A D S E}
    (hf : C.toDGFunctor = C'.toDGFunctor) (hh : HEq C.homotopy C'.homotopy) : C = C' := by
  cases C
  cases C'
  cases hf
  cases hh
  rfl

lemma restrict_extension (C : ContractedFunctor A D S E) :
    restrictContractedFunctor A D S (extension A C) = C := by
  apply ContractedFunctor.ext A
  · exact inclusion_comp_extension A C
  · exact heq_of_eq (funext (fun b => restrict_extension_homotopy A C b))

end SerrePositivity.DifferentialGraded.DGQuotient
