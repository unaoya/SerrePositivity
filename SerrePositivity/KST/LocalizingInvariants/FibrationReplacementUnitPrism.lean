module

public import SerrePositivity.KST.LocalizingInvariants.FibrationReplacementUnitInterval
public import SerrePositivity.KST.LocalizingInvariants.SpectrumPostcompositionPrism

/-!
概要：置換単位の相対区間を、同じ射影との合成三角形の実 prism へ移す。
方針：元の区間を合成対応へ送り、第一辺・固定第二辺・定数対角を全族として回収する。
規約：元の全区間と射影を保持。使われ方：右辺の全関手比較の二次の自然性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Spectra
open OmegaSpectrum
namespace SerrePositivity.KST.LocalizingInvariants.FibrationReplacementComparison

local instance unitPrismCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

variable {X Y X' Y' : OmegaSpectrum.{u}} (p : X ⟶ Y) (q : X' ⟶ Y')
  (a : X ⟶ X') (b : Y ⟶ Y') (h : p ≫ b = a ≫ q)

def unitTriangleEdge := SpectrumMappingPath.postTriangleEdge
  (fibrationReplacementProjection q) (unitPath p q a b h).path

lemma unitTriangleEdge_first :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.compositionCorrespondenceFirst (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex X)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (fibrationReplacementProjection q))).app (Opposite.op ⦋1⦌)
        (unitTriangleEdge p q a b h).edge =
      (SpectrumMappingPath.intervalEdge (unitPath p q a b h).path).edge :=
  SpectrumMappingPath.postTriangleEdge_first _ _

lemma unitTriangleEdge_diagonal :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.compositionCorrespondenceDiagonal (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex X)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (fibrationReplacementProjection q))).app (Opposite.op ⦋1⦌)
        (unitTriangleEdge p q a b h).edge =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingVertexOfEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (p ≫ b))) 1 :=
  SpectrumMappingPath.postTriangleEdge_diagonal_constant _ _ (p ≫ b)
    (unitPath_over_projection p q a b h)

def unitTrianglePrism : (Δ[2] : SSet.{u + 1}) ⊗ Δ[1] ⟶ Sp.{u} :=
  (Δ[2] ◁ SSet.yonedaEquiv.symm (unitTriangleEdge p q a b h).edge) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.compositionCorrespondenceEvaluation (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex X)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (fibrationReplacementProjection q))

lemma unitTrianglePrism_first :
    (stdSimplex.δ (2 : Fin 3) ▷ (Δ[1] : SSet.{u + 1})) ≫ unitTrianglePrism p q a b h =
      (unitHomotopy p q a b h).h := by
  rw [unitTrianglePrism, ← Category.assoc, ← whisker_exchange, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.compositionCorrespondenceEvaluation_first, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp]
  have he : SSet.yonedaEquiv.symm (unitTriangleEdge p q a b h).edge ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.compositionCorrespondenceFirst (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex X)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (fibrationReplacementProjection q)) =
    SSet.yonedaEquiv.symm (SpectrumMappingPath.intervalEdge (unitPath p q a b h).path).edge := by
    rw [SSet.yonedaEquiv_symm_comp]
    exact congrArg SSet.yonedaEquiv.symm (unitTriangleEdge_first p q a b h)
  rw [he]
  exact (SpectrumMappingPath.homotopy_map _).symm

lemma unitTrianglePrism_last :
    (stdSimplex.δ (0 : Fin 3) ▷ (Δ[1] : SSet.{u + 1})) ≫ unitTrianglePrism p q a b h =
      fst (Δ[1] : SSet.{u + 1}) Δ[1] ≫
        SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (fibrationReplacementProjection q)).edge := by
  rw [unitTrianglePrism, ← Category.assoc, ← whisker_exchange, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.compositionCorrespondenceEvaluation_last, ← Category.assoc, whiskerLeft_fst]
  rfl

lemma unitTrianglePrism_diagonal :
    (stdSimplex.δ (1 : Fin 3) ▷ (Δ[1] : SSet.{u + 1})) ≫ unitTrianglePrism p q a b h =
      fst (Δ[1] : SSet.{u + 1}) Δ[1] ≫
        SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (p ≫ b)).edge := by
  have he : SSet.yonedaEquiv.symm (unitTriangleEdge p q a b h).edge ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.compositionCorrespondenceDiagonal (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex X)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (fibrationReplacementProjection q)) =
    (SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingVertexOfEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (p ≫ b))) : (Δ[1] : SSet.{u + 1})
      ⟶ _) := by
    apply SSet.yonedaEquiv.injective
    rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
    exact unitTriangleEdge_diagonal p q a b h
  rw [unitTrianglePrism, ← Category.assoc, ← whisker_exchange, Category.assoc,
    ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.compositionCorrespondenceDiagonal_uncurry, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp,
    he, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.intervalMappingUncurry_const_vertex]
  have hv := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingEdgeVertexEquiv _ _).symm_apply_apply (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (p ≫ b))
  exact congrArg (fun e : Sp.Edge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex X) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex Y') ↦
    fst (Δ[1] : SSet.{u + 1}) Δ[1] ≫ SSet.yonedaEquiv.symm e.edge) hv

end SerrePositivity.KST.LocalizingInvariants.FibrationReplacementComparison
