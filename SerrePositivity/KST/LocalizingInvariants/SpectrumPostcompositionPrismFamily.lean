module

public import SerrePositivity.KST.LocalizingInvariants.SpectrumPostcompositionPrism
public import SerrePositivity.KST.LocalizingInvariants.SpectrumMappingIntervalConstant

/-!
概要：指定 BF 区間の後合成を、三つの指定された面を持つ全三角形 prism にする。
方針：同じ合成対応の辺を普遍三角形で評価し、三面を元の区間へ戻す。
規約：端点も区間も選び直さない。使われ方：PathLift の全射影区間との照合。
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
namespace SerrePositivity.KST.LocalizingInvariants.SpectrumMappingPath

local instance postFamilyCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

variable {X Y Z : OmegaSpectrum.{u}} (p : Y ⟶ Z) {f g : X ⟶ Y}
  (e : (mappingSpace X Y).Edge (vertexOfHom f) (vertexOfHom g))

def postTrianglePrism : (Δ[2] : SSet.{u + 1}) ⊗ Δ[1] ⟶ Sp.{u} :=
  (Δ[2] ◁ SSet.yonedaEquiv.symm (postTriangleEdge p e).edge) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.compositionCorrespondenceEvaluation (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex X) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge p)

lemma postTrianglePrism_first :
    (stdSimplex.δ (2 : Fin 3) ▷ (Δ[1] : SSet.{u + 1})) ≫ postTrianglePrism p e =
      (homotopy e).h := by
  rw [postTrianglePrism, ← Category.assoc, ← whisker_exchange, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.compositionCorrespondenceEvaluation_first, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp]
  have he : SSet.yonedaEquiv.symm (postTriangleEdge p e).edge ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.compositionCorrespondenceFirst (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex X) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge p) =
    SSet.yonedaEquiv.symm (intervalEdge e).edge := by
    rw [SSet.yonedaEquiv_symm_comp]
    exact congrArg SSet.yonedaEquiv.symm (postTriangleEdge_first p e)
  rw [he]
  exact (homotopy_map e).symm

lemma postTrianglePrism_last :
    (stdSimplex.δ (0 : Fin 3) ▷ (Δ[1] : SSet.{u + 1})) ≫ postTrianglePrism p e =
      fst (Δ[1] : SSet.{u + 1}) Δ[1] ≫
        SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge p).edge := by
  rw [postTrianglePrism, ← Category.assoc, ← whisker_exchange, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.compositionCorrespondenceEvaluation_last, ← Category.assoc, whiskerLeft_fst]
  rfl

lemma postTrianglePrism_diagonal :
    (stdSimplex.δ (1 : Fin 3) ▷ (Δ[1] : SSet.{u + 1})) ≫ postTrianglePrism p e =
      (homotopy (postEdge p e)).h := by
  have he : SSet.yonedaEquiv.symm (postTriangleEdge p e).edge ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.compositionCorrespondenceDiagonal (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex X) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge p) =
    SSet.yonedaEquiv.symm (intervalEdge (postEdge p e)).edge := by
    rw [SSet.yonedaEquiv_symm_comp]
    exact congrArg SSet.yonedaEquiv.symm (postTriangleEdge_diagonal p e)
  rw [postTrianglePrism, ← Category.assoc, ← whisker_exchange, Category.assoc,
    ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.compositionCorrespondenceDiagonal_uncurry, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp, he]
  exact (homotopy_map _).symm

lemma homotopy_map_congr {f₀ g₀ f₁ g₁ : X ⟶ Y}
    (e₀ : (mappingSpace X Y).Edge (vertexOfHom f₀) (vertexOfHom g₀))
    (e₁ : (mappingSpace X Y).Edge (vertexOfHom f₁) (vertexOfHom g₁))
    (h : e₀.edge = e₁.edge) : (homotopy e₀).h = (homotopy e₁).h := by
  exact (homotopy_map _).trans
    ((congrArg (fun z ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (SSet.yonedaEquiv.symm z))
      (intervalEdge_congr _ _ h)).trans (homotopy_map _).symm)

end SerrePositivity.KST.LocalizingInvariants.SpectrumMappingPath
