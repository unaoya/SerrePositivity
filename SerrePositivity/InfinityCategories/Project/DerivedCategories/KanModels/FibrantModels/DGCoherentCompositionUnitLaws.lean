module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.PinchedModels.PinchedClosedVertexSlice
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.FunctorComparisons.DGCoherentCompositionNaturality
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.PinchedModels.DGPinchedCompositionFamilyGeneral
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory MonoidalCategory CartesianMonoidalCategory DifferentialGraded
open SSet
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D]

lemma dgStandardUnit_yoneda (x : D) (n : ℕ) :
    SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardUnit (R := A) (D := D) x n) =
      toUnit (Δ[n] : SSet.{u}) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardUnitMap (R := A) (D := D) x := by
  have h := SSet.yonedaEquiv_symm_comp
    (X := (𝟙_ SSet.{u})) (n := ⦋n⦌) PUnit.unit (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardUnitMap (R := A) (D := D) x)
  exact h.symm

lemma dgStandardUnitMap_eq_id (x : D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardUnitMap (R := A) (D := D) x =
      eId SSet (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) x) := rfl

lemma dgStandardUnit_lift_comp {x z : D} {K : SSet.{u}}
    (h : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomSpace (R := A) (D := D) x z) :
    lift (toUnit K ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardUnitMap (R := A) (D := D) x) h ≫
      eComp SSet (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) x)
        (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) x) (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) z) = h := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro a
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.simplicialHom_id_comp_app (ForgetEnrichment.of (Complex A) x)
    (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) z) _ (h.app _ a)

lemma dgCoherentCompositionObj_first_unit (x z : _root_.SerrePositivity.DifferentialGraded.ClosedCategory A D) {n : ℕ}
    (t : Fin (n + 1) →o Fin 2) (i : Fin (n + 2)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionObj x x z t i = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj x z i := by
  induction i using Fin.lastCases <;>
    simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionObj, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj,
      Fin.lastCases_last, Fin.lastCases_castSucc, ite_self]

lemma dgCoherentCompositionSimplex_first_unit {x z : D} {n : ℕ}
    (τ : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StandardSimplex A x z n) (t : Fin (n + 1) →o Fin 2) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionSimplex (C := ClosedCategory A D)
      (X := ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) x) (Y := ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) x)
      (Z := ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) z)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardUnit (R := A) (D := D) x n) τ t =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonSimplex (C := ClosedCategory A D)
        (X := ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) x) (Y := ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) z) τ := by
  let X := ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) x
  let Z := ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) z
  change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionSimplex (X := X) (Y := X) (Z := Z)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardUnit (R := A) (D := D) x n) τ t =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonSimplex (X := X) (Y := Z) τ
  apply EnrichedFunctor.ext SSet
    (fun i => dgCoherentCompositionObj_first_unit A D X Z t i.as.down)
  rintro ⟨⟨i⟩⟩ ⟨⟨j⟩⟩
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionSimplex, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonSimplex]
  induction i using Fin.lastCases <;> induction j using Fin.lastCases
  case last.last =>
    simp -implicitDefEqProofs +instances only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj,
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionObj, Fin.isValue, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionHom, eq_mpr_eq_cast, ite_self,
      Fin.lastCases_last, congrArg_cast_hom_right, Category.assoc, eqToHom_naturality,
      eqToHom_refl, Category.id_comp, Fin.lastCases_castSucc, dite_eq_ite,
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonHom]
  case last.cast j =>
    simp -implicitDefEqProofs +instances only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj,
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionObj, Fin.isValue, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionHom, eq_mpr_eq_cast, ite_self,
      Fin.lastCases_last, congrArg_cast_hom_right, Category.assoc, eqToHom_naturality,
      eqToHom_refl, Category.id_comp, Fin.lastCases_castSucc, dite_eq_ite,
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonHom]
  case cast.last i =>
    by_cases hi : t i = 0
    · simp -implicitDefEqProofs +instances only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj,
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionObj, Fin.isValue, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionHom, eq_mpr_eq_cast, ite_self,
        Fin.lastCases_last, congrArg_cast_hom_right, Category.assoc, eqToHom_naturality,
        eqToHom_refl, Category.id_comp, Fin.lastCases_castSucc, dite_eq_ite, hi, ↓reduceDIte,
        eqToHom_trans, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonHom]
      erw [dgStandardUnit_yoneda A D x n]
      simp only [← Category.assoc, comp_toUnit]
      erw [dgStandardUnit_lift_comp A D]
    · simp -implicitDefEqProofs +instances only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj,
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionObj, Fin.isValue, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionHom, eq_mpr_eq_cast, ite_self,
        Fin.lastCases_last, congrArg_cast_hom_right, Category.assoc, eqToHom_naturality,
        eqToHom_refl, Category.id_comp, Fin.lastCases_castSucc, dite_eq_ite, hi, ↓reduceDIte,
        eqToHom_trans, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonHom]
  case cast.cast i j =>
    by_cases hi : t i = 0 <;> by_cases hj : t j = 0
    · simp -implicitDefEqProofs +instances only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj,
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionObj, Fin.isValue, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionHom, eq_mpr_eq_cast, ite_self,
        Fin.lastCases_last, congrArg_cast_hom_right, Category.assoc, eqToHom_naturality,
        eqToHom_refl, Category.id_comp, Fin.lastCases_castSucc, dite_eq_ite, hj, ↓reduceIte,
        ↓reduceDIte, hi, eqToHom_trans, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonHom]
    · simp -implicitDefEqProofs +instances only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj,
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionObj, Fin.isValue, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionHom, eq_mpr_eq_cast, ite_self,
        Fin.lastCases_last, congrArg_cast_hom_right, Category.assoc, eqToHom_naturality,
        eqToHom_refl, Category.id_comp, Fin.lastCases_castSucc, dite_eq_ite, hj, ↓reduceIte,
        ↓reduceDIte, hi, eqToHom_trans, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonHom]
      erw [dgStandardUnit_yoneda A D x n]
      rfl
    · apply SSet.hom_ext
      intro d
      apply ConcreteCategory.hom_ext
      intro P
      exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCut_backward_false t hi hj (P.obj 0)).elim
    · simp -implicitDefEqProofs +instances only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj,
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionObj, Fin.isValue, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionHom, eq_mpr_eq_cast, ite_self,
        Fin.lastCases_last, congrArg_cast_hom_right, Category.assoc, eqToHom_naturality,
        eqToHom_refl, Category.id_comp, Fin.lastCases_castSucc, dite_eq_ite, hj, ↓reduceIte,
        ↓reduceDIte, hi, eqToHom_trans, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonHom]

lemma dgStandardPinched_unit_vertex (x : D) :
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomPinchedIso (R := A) (D := D) x x).inv.app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedVertex A D (𝟙 (ForgetEnrichment.of (Complex A) x)))).down =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardUnit (R := A) (D := D) x 0 := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardZeroEquiv (R := A) (D := D) x x).injective
  erw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardZeroEval_unit]
  apply Subtype.ext
  change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.degreeSign 0 • (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedVertex A D (𝟙 (ForgetEnrichment.of (Complex A) x)))).val.component
      Finset.univ 0 Finset.univ_nonempty (by simp) = _
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.degreeSign, Int.reduceNeg, Nat.choose_zero_succ, pow_zero, Nat.reduceAdd,
    Finset.univ_unique, Fin.default_eq_zero, Fin.isValue, one_smul]
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearData_component_heq
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedVertex A D (𝟙 (ForgetEnrichment.of (Complex A) x)))
    ({0} : Finset (Fin 1)) 0 (by simp) (by simp)
  apply eq_of_heq
  refine h.trans (HEq.trans (b :=
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedVertex A D (𝟙 (ForgetEnrichment.of (Complex A) x))).val.hom
      Finset.univ 0 1 0 (by decide) (by decide) (by decide) (by decide)) ?_ ?_)
  · let s := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedVertex A D (𝟙 (ForgetEnrichment.of (Complex A) x))
    exact s.val.toSimplexData.hom_heq_of_indices_degree
      (J := Finset.univ) (c := 0) (d := 1) (l := 0)
      (hJ := by decide) (hc := by decide) (hd := by decide) (hl := by decide)
      (by decide) (by decide) rfl rfl
  · change HEq (_root_.SerrePositivity.DifferentialGraded.closedHomEquiv A D _ _ (𝟙 (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) x))).val
      (_root_.SerrePositivity.DifferentialGraded.unitElement A x).val
    exact heq_of_eq (congrArg Subtype.val
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.closedHom_id (ForgetEnrichment.of (Complex A) x)))

end SerrePositivity.InfinityCategories.Project.DerivedCategories
