module

public import SerrePositivity.KST.LocalizingInvariants.FiberMappingPathLift
public import SerrePositivity.KST.LocalizingInvariants.SpectrumPostcompositionPrismFamily

/-!
概要：PathLift の指定射影区間を、元の Sp 区間を対角に持つ合成三角形の prism にする。
方針：over の実射の等式を一単体へ戻し、同じ後合成 prism の対角を同定する。
規約：充填の選択を変更しない。使われ方：厳密化した右辺比較と元の指定 prism の比較。
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
namespace SerrePositivity.KST.LocalizingInvariants.FiberMapping.PathLift

local instance liftPrismCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

variable {X Y Z : OmegaSpectrum.{u}} {p : Y ⟶ Z} {a : X ⟶ Y} {b : X ⟶ Z}
  {γ : (mappingSpace X Z).Edge (vertexOfHom (a ≫ p)) (vertexOfHom b)}
  (L : PathLift p a b γ)

lemma over_edge : (SpectrumMappingAcyclic.post X p).app (Opposite.op ⦋1⦌) L.path.edge =
    γ.edge := by
  have he := congrArg SSet.yonedaEquiv L.over
  rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply] at he
  exact he

def trianglePrism : (Δ[2] : SSet.{u + 1}) ⊗ Δ[1] ⟶ Sp.{u} :=
  SpectrumMappingPath.postTrianglePrism p L.path

lemma trianglePrism_first :
    (stdSimplex.δ (2 : Fin 3) ▷ (Δ[1] : SSet.{u + 1})) ≫ L.trianglePrism =
      (SpectrumMappingPath.homotopy L.path).h :=
  SpectrumMappingPath.postTrianglePrism_first _ _

lemma trianglePrism_last :
    (stdSimplex.δ (0 : Fin 3) ▷ (Δ[1] : SSet.{u + 1})) ≫ L.trianglePrism =
      fst (Δ[1] : SSet.{u + 1}) Δ[1] ≫ SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge p).edge :=
  SpectrumMappingPath.postTrianglePrism_last _ _

lemma trianglePrism_diagonal :
    (stdSimplex.δ (1 : Fin 3) ▷ (Δ[1] : SSet.{u + 1})) ≫ L.trianglePrism =
      (SpectrumMappingPath.homotopy γ).h := by
  exact (SpectrumMappingPath.postTrianglePrism_diagonal p L.path).trans
    (SpectrumMappingPath.homotopy_map_congr _ _ L.over_edge)

end SerrePositivity.KST.LocalizingInvariants.FiberMapping.PathLift
