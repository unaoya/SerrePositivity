module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.FixedFractionTriangles
public import SerrePositivity.KST.LocalizingInvariants.TriangleThirdEdgeBoundary
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.RightIntervalEquivalence

/-!
概要：記憶した実三角形の第三辺を直接評価し、元の分数写像空間比較との整合を保つ。
方針：horn の一致から端点を固定し、厳密切断と射影の可逆比較で選択との整合を導く。
規約：直接評価の同値性と元の比較の同値性は同値。両者の同値性自体は未証明。
使われ方：相対 Ore による分数写像空間比較の次の充填問題。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
end SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.InfinityCategories.Derived.Verdier.Fractions
open SerrePositivity.KST.LocalizingInvariants
variable {X Q : SSet.{u}} [Quasicategory Q] (F : X ⟶ Q) (W : Set (X _⦋1⦌))
  (hF : InvertsEdges F W) (x y : X _⦋0⦌)

def fixedFractionTriangleEdge : _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fixedFractionTriangles F W hF x y ⟶
    (ihom (Δ[1] : SSet.{u})).obj Q :=
  _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fixedFractionTriangleFamily F W hF x y ≫ (pre (stdSimplex.δ (0 : Fin 3))).app Q

lemma fixedFractionTriangleEdge_boundary : _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fixedFractionTriangleEdge F W hF x y ≫
    (pre (boundary 1).ι).app Q = SSet.const (functorVertex
      (intervalMappingBoundary (F.app (Opposite.op ⦋0⦌) x) (F.app (Opposite.op ⦋0⦌) y))) := by
  have hs : _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fixedFractionTriangleFamily F W hF x y ≫ (pre (horn 2 0).ι).app Q =
      (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fixedFractionTriangleProjection F W hF x y ≫ fixedMarkedSpanInclusion X W x y ≫
        fractionEvaluationTriangle F W hF) ≫ (pre (horn 2 0).ι).app Q := by
    rw [_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fixedFractionTriangleFamily_span]
    simp only [Category.assoc, fractionEvaluationTriangle_span]
  rw [_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fixedFractionTriangleEdge, triangleThirdEdge_boundary_eq hs]
  change (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fixedFractionTriangleProjection F W hF x y ≫ fixedMarkedSpanInclusion X W x y ≫
    fractionSpanEvaluation F W hF) ≫ (pre (boundary 1).ι).app Q = _
  rw [Category.assoc, Category.assoc, fractionSpanEvaluation_boundary,
    ← Category.assoc (fixedMarkedSpanInclusion X W x y), fixedMarkedSpanInclusion,
    vertexFiberι_comp, SSet.const_comp, SSet.comp_const]
  change SSet.const (functorVertex (intervalMappingBoundary x y ≫ F)) = _
  rw [intervalMappingBoundary_postcomp]

def fixedFractionTriangleEvaluation : _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fixedFractionTriangles F W hF x y ⟶
    intervalMappingSpace (F.app (Opposite.op ⦋0⦌) x) (F.app (Opposite.op ⦋0⦌) y) :=
  vertexFiberLift _ _ (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fixedFractionTriangleEdge F W hF x y)
    (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fixedFractionTriangleEdge_boundary F W hF x y)

lemma fixedFractionTriangleSection_evaluation : _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fixedFractionTriangleSection F W hF x y ≫
    _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fixedFractionTriangleEvaluation F W hF x y = fixedFractionEvaluation F W hF x y := by
  apply vertexFiber_hom_ext ((pre (boundary 1).ι).app Q)
    (functorVertex (intervalMappingBoundary (F.app (Opposite.op ⦋0⦌) x)
      (F.app (Opposite.op ⦋0⦌) y)))
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fixedFractionTriangleEvaluation, vertexFiberLift_ι,
    _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fixedFractionTriangleEdge, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fixedFractionTriangleSection_family,
    fixedFractionEvaluation_inclusion]
  rfl

def fixedFractionTriangleEvaluationIso : FunctorIso
    (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fixedFractionTriangleProjection F W hF x y ≫ fixedFractionEvaluation F W hF x y)
    (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fixedFractionTriangleEvaluation F W hF x y) := by
  have h := functorIsoOfTrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fixedFractionTriangleProjection F W hF x y)
    (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fixedFractionTriangleProjection F W hF x y ≫ _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fixedFractionTriangleSection F W hF x y)
    (𝟙 _) (by rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fixedFractionTriangleSection_projection,
      Category.comp_id, Category.id_comp])
  have e := FunctorIso.postcomp h (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fixedFractionTriangleEvaluation F W hF x y)
  simpa only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fixedFractionTriangleSection_evaluation, Category.id_comp] using e

lemma fixedFractionTriangleEvaluation_equivalence_iff :
    IsSimplicialHomotopyEquivalence
      (_root_.SerrePositivity.InfinityCategories.Derived.Localization.groupoidCompletionEvaluation (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fixedFractionTriangleEvaluation F W hF x y)) ↔
    IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionMappingComparison F W hF x y) := by
  have e := _root_.SerrePositivity.InfinityCategories.Derived.Localization.groupoidCompletionEvaluation_functorIso (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fixedFractionTriangleEvaluationIso F W hF x y)
  constructor
  · intro h
    have hp := (h.isQCatEquivalence.ofFunctorIso e.symm).isSimplicialHomotopyEquivalence
    exact (_root_.SerrePositivity.InfinityCategories.Derived.Localization.groupoidCompletionEvaluation_trivialKanFibration_iff _ _).mp hp
  · intro h
    have hp := (_root_.SerrePositivity.InfinityCategories.Derived.Localization.groupoidCompletionEvaluation_trivialKanFibration_iff
      (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fixedFractionTriangleProjection F W hF x y) (fixedFractionEvaluation F W hF x y)).mpr h
    exact (hp.isQCatEquivalence.ofFunctorIso e).isSimplicialHomotopyEquivalence

lemma fractionMappingComparison_equivalence_iff_pinched :
    IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionMappingComparison F W hF x y) ↔
    IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionPinchedMappingComparison F W hF x y) := by
  have hm := pinchedHomToIntervalMappingSpace_isQCatEquivalence
    (F.app (Opposite.op ⦋0⦌) x) (F.app (Opposite.op ⦋0⦌) y)
  have e := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionMappingModelComparisonIso F W hF x y
  constructor
  · intro h
    have hh := hm.cancel_right (h.isQCatEquivalence.ofFunctorIso e.symm)
    exact hh.isSimplicialHomotopyEquivalence
  · intro h
    exact ((h.isQCatEquivalence.comp hm).ofFunctorIso e).isSimplicialHomotopyEquivalence

lemma fixedFractionTriangleEvaluation_equivalence_iff_pinched :
    IsSimplicialHomotopyEquivalence
      (_root_.SerrePositivity.InfinityCategories.Derived.Localization.groupoidCompletionEvaluation (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fixedFractionTriangleEvaluation F W hF x y)) ↔
    IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionPinchedMappingComparison F W hF x y) :=
  (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fixedFractionTriangleEvaluation_equivalence_iff F W hF x y).trans
    (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionMappingComparison_equivalence_iff_pinched F W hF x y)

end SerrePositivity.InfinityCategories.Derived.Verdier.Fractions

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fixedFractionTriangleEdge (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.fixedFractionTriangleEdge := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fixedFractionTriangleEdge

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.fixedFractionTriangleEdge_boundary := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fixedFractionTriangleEdge_boundary

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fixedFractionTriangleEvaluation (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.fixedFractionTriangleEvaluation := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fixedFractionTriangleEvaluation

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fixedFractionTriangleEvaluationIso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.fixedFractionTriangleEvaluationIso := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fixedFractionTriangleEvaluationIso

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.fixedFractionTriangleEvaluation_equivalence_iff := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fixedFractionTriangleEvaluation_equivalence_iff

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.fixedFractionTriangleEvaluation_equivalence_iff_pinched := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fixedFractionTriangleEvaluation_equivalence_iff_pinched

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.fixedFractionTriangleSection_evaluation := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fixedFractionTriangleSection_evaluation

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.fractionMappingComparison_equivalence_iff_pinched := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionMappingComparison_equivalence_iff_pinched

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.fixedFractionTriangleEdge._proof_1 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fixedFractionTriangleEdge._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.fixedFractionTriangleEdge.eq_1 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fixedFractionTriangleEdge.eq_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.fixedFractionTriangleEvaluation.congr_simp := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fixedFractionTriangleEvaluation.congr_simp

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.fixedFractionTriangleEvaluation.eq_1 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fixedFractionTriangleEvaluation.eq_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.fixedFractionTriangleEvaluationIso._proof_1 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fixedFractionTriangleEvaluationIso._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.fixedFractionTriangleEvaluationIso._proof_2 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fixedFractionTriangleEvaluationIso._proof_2
