module
public import SerrePositivity.InfinityCategories.Derived.PinchedClosedVertexSlice
public import SerrePositivity.InfinityCategories.Derived.DGCoherentCompositionNaturality
public import SerrePositivity.InfinityCategories.Derived.DGPinchedCompositionFamilyGeneral
/-!
概要：coherent な dg 合成単体の厳密な単位退化表示を与える。
方針：標準 Hom の単位を豊穣恒等に同定し、同じ全 coherent 図式を比較する。
規約：Small 仮定を置かず、全単体・全時刻と端点を保持する。
使われ方：D2 の合成三角形に生じる恒等合成の除去。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory CartesianMonoidalCategory DifferentialGraded
open DGNerve DoldKanComparison SSet
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

lemma dgStandardUnit_yoneda (x : D) (n : ℕ) :
    SSet.yonedaEquiv.symm (standardUnit (R := A) (D := D) x n) =
      toUnit (Δ[n] : SSet.{u}) ≫ standardUnitMap (R := A) (D := D) x := by
  have h := SSet.yonedaEquiv_symm_comp
    (X := (𝟙_ SSet.{u})) (n := ⦋n⦌) PUnit.unit (standardUnitMap (R := A) (D := D) x)
  exact h.symm

lemma dgStandardUnitMap_eq_id (x : D) :
    standardUnitMap (R := A) (D := D) x =
      eId SSet (ForgetEnrichment.of (Complex A) x) := rfl

lemma dgStandardUnit_lift_comp {x z : D} {K : SSet.{u}}
    (h : K ⟶ standardHomSpace (R := A) (D := D) x z) :
    lift (toUnit K ≫ standardUnitMap (R := A) (D := D) x) h ≫
      eComp SSet (ForgetEnrichment.of (Complex A) x)
        (ForgetEnrichment.of (Complex A) x) (ForgetEnrichment.of (Complex A) z) = h := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro a
  exact simplicialHom_id_comp_app (ForgetEnrichment.of (Complex A) x)
    (ForgetEnrichment.of (Complex A) z) _ (h.app _ a)

lemma dgCoherentCompositionObj_first_unit (x z : ClosedCategory A D) {n : ℕ}
    (t : Fin (n + 1) →o Fin 2) (i : Fin (n + 2)) :
    coherentCompositionObj x x z t i = coherentHomComparisonObj x z i := by
  induction i using Fin.lastCases <;>
    simp only [coherentCompositionObj, coherentHomComparisonObj,
      Fin.lastCases_last, Fin.lastCases_castSucc, ite_self]

lemma dgCoherentCompositionSimplex_first_unit {x z : D} {n : ℕ}
    (τ : StandardSimplex A x z n) (t : Fin (n + 1) →o Fin 2) :
    coherentCompositionSimplex (C := ClosedCategory A D)
      (X := ForgetEnrichment.of (Complex A) x) (Y := ForgetEnrichment.of (Complex A) x)
      (Z := ForgetEnrichment.of (Complex A) z)
      (standardUnit (R := A) (D := D) x n) τ t =
      coherentHomComparisonSimplex (C := ClosedCategory A D)
        (X := ForgetEnrichment.of (Complex A) x) (Y := ForgetEnrichment.of (Complex A) z) τ := by
  let X := ForgetEnrichment.of (Complex A) x
  let Z := ForgetEnrichment.of (Complex A) z
  change coherentCompositionSimplex (X := X) (Y := X) (Z := Z)
    (standardUnit (R := A) (D := D) x n) τ t =
      coherentHomComparisonSimplex (X := X) (Y := Z) τ
  apply EnrichedFunctor.ext SSet
    (fun i => dgCoherentCompositionObj_first_unit A D X Z t i.as.down)
  rintro ⟨⟨i⟩⟩ ⟨⟨j⟩⟩
  dsimp only [coherentCompositionSimplex, coherentHomComparisonSimplex]
  induction i using Fin.lastCases <;> induction j using Fin.lastCases
  case last.last =>
    simp -implicitDefEqProofs +instances only [coherentHomComparisonObj,
      coherentCompositionObj, Fin.isValue, coherentCompositionHom, eq_mpr_eq_cast, ite_self,
      Fin.lastCases_last, congrArg_cast_hom_right, Category.assoc, eqToHom_naturality,
      eqToHom_refl, Category.id_comp, Fin.lastCases_castSucc, dite_eq_ite,
      coherentHomComparisonHom]
  case last.cast j =>
    simp -implicitDefEqProofs +instances only [coherentHomComparisonObj,
      coherentCompositionObj, Fin.isValue, coherentCompositionHom, eq_mpr_eq_cast, ite_self,
      Fin.lastCases_last, congrArg_cast_hom_right, Category.assoc, eqToHom_naturality,
      eqToHom_refl, Category.id_comp, Fin.lastCases_castSucc, dite_eq_ite,
      coherentHomComparisonHom]
  case cast.last i =>
    by_cases hi : t i = 0
    · simp -implicitDefEqProofs +instances only [coherentHomComparisonObj,
        coherentCompositionObj, Fin.isValue, coherentCompositionHom, eq_mpr_eq_cast, ite_self,
        Fin.lastCases_last, congrArg_cast_hom_right, Category.assoc, eqToHom_naturality,
        eqToHom_refl, Category.id_comp, Fin.lastCases_castSucc, dite_eq_ite, hi, ↓reduceDIte,
        eqToHom_trans, coherentHomComparisonHom]
      erw [dgStandardUnit_yoneda A D x n]
      simp only [← Category.assoc, comp_toUnit]
      erw [dgStandardUnit_lift_comp A D]
    · simp -implicitDefEqProofs +instances only [coherentHomComparisonObj,
        coherentCompositionObj, Fin.isValue, coherentCompositionHom, eq_mpr_eq_cast, ite_self,
        Fin.lastCases_last, congrArg_cast_hom_right, Category.assoc, eqToHom_naturality,
        eqToHom_refl, Category.id_comp, Fin.lastCases_castSucc, dite_eq_ite, hi, ↓reduceDIte,
        eqToHom_trans, coherentHomComparisonHom]
  case cast.cast i j =>
    by_cases hi : t i = 0 <;> by_cases hj : t j = 0
    · simp -implicitDefEqProofs +instances only [coherentHomComparisonObj,
        coherentCompositionObj, Fin.isValue, coherentCompositionHom, eq_mpr_eq_cast, ite_self,
        Fin.lastCases_last, congrArg_cast_hom_right, Category.assoc, eqToHom_naturality,
        eqToHom_refl, Category.id_comp, Fin.lastCases_castSucc, dite_eq_ite, hj, ↓reduceIte,
        ↓reduceDIte, hi, eqToHom_trans, coherentHomComparisonHom]
    · simp -implicitDefEqProofs +instances only [coherentHomComparisonObj,
        coherentCompositionObj, Fin.isValue, coherentCompositionHom, eq_mpr_eq_cast, ite_self,
        Fin.lastCases_last, congrArg_cast_hom_right, Category.assoc, eqToHom_naturality,
        eqToHom_refl, Category.id_comp, Fin.lastCases_castSucc, dite_eq_ite, hj, ↓reduceIte,
        ↓reduceDIte, hi, eqToHom_trans, coherentHomComparisonHom]
      erw [dgStandardUnit_yoneda A D x n]
      rfl
    · apply SSet.hom_ext
      intro d
      apply ConcreteCategory.hom_ext
      intro P
      exact (pathCut_backward_false t hi hj (P.obj 0)).elim
    · simp -implicitDefEqProofs +instances only [coherentHomComparisonObj,
        coherentCompositionObj, Fin.isValue, coherentCompositionHom, eq_mpr_eq_cast, ite_self,
        Fin.lastCases_last, congrArg_cast_hom_right, Category.assoc, eqToHom_naturality,
        eqToHom_refl, Category.id_comp, Fin.lastCases_castSucc, dite_eq_ite, hj, ↓reduceIte,
        ↓reduceDIte, hi, eqToHom_trans, coherentHomComparisonHom]

lemma dgStandardPinched_unit_vertex (x : D) :
    ((standardHomPinchedIso (R := A) (D := D) x x).inv.app (Opposite.op ⦋0⦌)
      (pinchedClosedVertex A D (𝟙 (ForgetEnrichment.of (Complex A) x)))).down =
      standardUnit (R := A) (D := D) x 0 := by
  apply (standardZeroEquiv (R := A) (D := D) x x).injective
  erw [standardZeroEval_unit]
  apply Subtype.ext
  change degreeSign 0 • (DGNerve.PinchedHom.toLinearSimplex
    (pinchedClosedVertex A D (𝟙 (ForgetEnrichment.of (Complex A) x)))).val.component
      Finset.univ 0 Finset.univ_nonempty (by simp) = _
  simp only [degreeSign, Int.reduceNeg, Nat.choose_zero_succ, pow_zero, Nat.reduceAdd,
    Finset.univ_unique, Fin.default_eq_zero, Fin.isValue, one_smul]
  have h := DGNerve.PinchedHom.toLinearData_component_heq
    (pinchedClosedVertex A D (𝟙 (ForgetEnrichment.of (Complex A) x)))
    ({0} : Finset (Fin 1)) 0 (by simp) (by simp)
  apply eq_of_heq
  refine h.trans (HEq.trans (b :=
    (pinchedClosedVertex A D (𝟙 (ForgetEnrichment.of (Complex A) x))).val.hom
      Finset.univ 0 1 0 (by decide) (by decide) (by decide) (by decide)) ?_ ?_)
  · let s := pinchedClosedVertex A D (𝟙 (ForgetEnrichment.of (Complex A) x))
    exact s.val.toSimplexData.hom_heq_of_indices_degree
      (J := Finset.univ) (c := 0) (d := 1) (l := 0)
      (hJ := by decide) (hc := by decide) (hd := by decide) (hl := by decide)
      (by decide) (by decide) rfl rfl
  · change HEq (closedHomEquiv A D _ _ (𝟙 (ForgetEnrichment.of (Complex A) x))).val
      (unitElement A x).val
    exact heq_of_eq (congrArg Subtype.val
      (DGNerve.HomotopyComparison.closedHom_id (ForgetEnrichment.of (Complex A) x)))

end SerrePositivity.InfinityCategories
