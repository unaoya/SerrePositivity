module
public import SerrePositivity.KST.SConstruction.DGKappaNativeBFNativeObjects
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.NerveHomEdgeNaturality

/-!
概要：同じ実 BF 全四角形の四辺を、元四射から同時構成した BF 射として回収する。
方針：充満包含の nerve の単射性で元境界を制限し、全 BF 作用を適用する。
規約：旧 kSpectrumMap との厳密等式を課さない。使われ方：K-B の新四辺方式。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet DifferentialGraded InfinityCategories
open NonConnective Spectra LocalizingInvariants HomotopyLimits
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : PerfDGInput.{u, max (u + 1) v} R)
  {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)

local instance nativeCoherentBFBoundaryTarget_simplicialCategory :
    SimplicialCategory OmegaSpectrum.{w} := OmegaSpectrum.simplicialCategory

/-- 概要：元の底・右・左・上の四境界包含。
方針：同じ標準四角形の元辺を並べる。
規約：元 native 四射と同じ順序。使われ方：四辺同時回収。 -/
def dgKappaNativeBFSquareEdge : Fin 4 →
    ((Δ[1] : SSet.{max (u + 1) v + 1}) ⟶ Δ[1] ⊗ Δ[1]) :=
  ![_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge]

/-- 概要：同じ元四角形の四辺は元四完全射を回収する。
方針：元提示の包含・商と指定二零辺を使う。
規約：元一次単体の等号。使われ方：有限入力への境界制限。 -/
lemma dgKappaNativeBFNativeSquare_boundary (e : Fin 4) :
    dgKappaNativeBFSquareEdge.{u, v} e ≫
      (dgKappaNativeVerdierDiagram.{u, v} R D I).square =
        SSet.yonedaEquiv.symm
          (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (dgKappaNativeBFNativeArrow.{u, v} R D I e).hom).edge := by
  fin_cases e
  · exact (dgKappaNativeVerdierDiagram.{u, v} R D I).bottom_edge
  · exact (dgKappaNativeVerdierDiagram.{u, v} R D I).right_edge
  · exact VerdierSequence.presentation_left (dgKappaNativeVerdierSequence.{u, v} R D I)
  · exact VerdierSequence.presentation_top (dgKappaNativeVerdierSequence.{u, v} R D I)

/-- 概要：同じ有限入力の四射を包含すると元の四辺に厳密に戻る。
方針：同じ Hom の恒等包含を単位パラメータで評価する。
規約：全一単体の等号。使われ方：元境界の一意な制限。 -/
lemma dgKappaNativeBFFiniteNativeArrow_inclusion (e : Fin 4) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (dgKappaNativeBFFiniteInclusion.{u, v} R D I)).app
      (Opposite.op ⦋1⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgKappaNativeBFFiniteNativeArrow.{u, v} R D I e).hom).edge =
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (dgKappaNativeBFNativeArrow.{u, v} R D I e).hom).edge := by
  fin_cases e <;>
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveMap_edge_of_homEquiv
      (dgKappaNativeBFFiniteInclusion.{u, v} R D I) _ _ (Category.comp_id _)

/-- 概要：同じ元四辺は有限入力の同じ四射へ厳密に制限される。
方針：充満包含の nerve の単射性と元の四辺の回収を使う。
規約：辺を選び直さない。使われ方：実 Φ の四辺。 -/
lemma dgKappaNativeBFFiniteSquare_boundary (e : Fin 4) :
    dgKappaNativeBFSquareEdge.{u, v} e ≫ dgKappaNativeBFFiniteSquare.{u, v} R D I =
      SSet.yonedaEquiv.symm
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgKappaNativeBFFiniteNativeArrow.{u, v} R D I e).hom).edge := by
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentFullSubcategoryInclusion
    (dgKappaNativeBFVertexProperty.{u, v} R D I))).mp
  have hl := (Category.assoc (dgKappaNativeBFSquareEdge.{u, v} e)
    (dgKappaNativeBFFiniteSquare.{u, v} R D I)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (dgKappaNativeBFFiniteInclusion.{u, v} R D I))).trans
      (congrArg (fun k => dgKappaNativeBFSquareEdge.{u, v} e ≫ k)
        (dgKappaNativeBFFiniteSquare_inclusion.{u, v} R D I))
  have hr := (SSet.yonedaEquiv_symm_comp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgKappaNativeBFFiniteNativeArrow.{u, v} R D I e).hom).edge
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (dgKappaNativeBFFiniteInclusion.{u, v} R D I))).trans
      (congrArg SSet.yonedaEquiv.symm
        (dgKappaNativeBFFiniteNativeArrow_inclusion.{u, v} R D I e))
  exact hl.trans ((dgKappaNativeBFNativeSquare_boundary.{u, v} R D I e).trans hr.symm)

/-- 概要：実 Φ の四辺は同時構成した四 BF 射そのもの。
方針：同じ元四辺の全 Hom 作用を BF 豊穣関手へ写す。
規約：旧辺の全 Sp 写像空間比較を要求しない。使われ方：K-B の有限四角形境界。 -/
lemma dgKappaNativeCoherentBFSquare_boundary (e : Fin 4) :
    dgKappaNativeBFSquareEdge.{u, v} e ≫ dgKappaNativeCoherentBFSquare.{u, v} R D I =
      SSet.yonedaEquiv.symm
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgKappaNativeCoherentBFArrow.{u, v} R D I e).hom).edge := by
  have he := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveMap_edge_of_homEquiv
    (dgKappaNativeBFEnrichedFunctor.{u, v} R D I)
    (dgKappaNativeBFFiniteNativeArrow.{u, v} R D I e).hom
    (dgKappaNativeCoherentBFArrow.{u, v} R D I e).hom
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.strictSimplicialOrdinaryMap_hom _ _).symm
  exact (Category.assoc (dgKappaNativeBFSquareEdge.{u, v} e)
    (dgKappaNativeBFFiniteSquare.{u, v} R D I)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (dgKappaNativeBFEnrichedFunctor.{u, v} R D I))).symm.trans
      ((congrArg (fun k => k ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap
        (dgKappaNativeBFEnrichedFunctor.{u, v} R D I))
          (dgKappaNativeBFFiniteSquare_boundary.{u, v} R D I e)).trans
        ((SSet.yonedaEquiv_symm_comp _ _).trans (congrArg SSet.yonedaEquiv.symm he)))

end SerrePositivity.KST.SConstruction
