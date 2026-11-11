module

public import SerrePositivity.KST.LocalizingInvariants.SpectrumTriangleMappingEdge
public import SerrePositivity.KST.Spectra.FibrationDifferenceTriangleLift

/-!
概要：二つの Sp 三角形の共通対角辺から、両合成を結ぶ BF 写像空間の区間を作る。
方針：指定した豊穣二辺を外ホーンで充填し、同じ三角形をデータに保持する。
規約：π₀ の等式から区間を選び直さない。使われ方：coherent 正方形の厳密化。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Spectra
open OmegaSpectrum
namespace SerrePositivity.KST.LocalizingInvariants.SpectrumMappingPrism

local instance triangleDifferenceSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

variable {X Z : OmegaSpectrum.{u}} {h f g : X ⟶ Z}
  (H : (mappingSpace X Z).Edge (vertexOfHom h) (vertexOfHom f))
  (V : (mappingSpace X Z).Edge (vertexOfHom h) (vertexOfHom g))

structure TriangleDifference where
  edge : (mappingSpace X Z).Edge (vertexOfHom f) (vertexOfHom g)
  triangle : SSet.Edge.CompStruct H edge V

def triangleDifference : TriangleDifference H V := by
  let p := terminal.from (mappingSpace X Z)
  have hp : J.rlp p := (fibration_iff _).1 inferInstance
  let hex := exists_difference_triangle_lift p hp H V (terminal.from (Δ[2] : SSet.{u}))
    (Subsingleton.elim _ _) (Subsingleton.elim _ _)
  exact ⟨hex.choose, hex.choose_spec.choose⟩

namespace TriangleDifference

variable (C : TriangleDifference H V)

lemma first : stdSimplex.δ (2 : Fin 3) ≫ SSet.yonedaEquiv.symm C.triangle.simplex =
    SSet.yonedaEquiv.symm H.edge := SSet.Edge.CompStruct.δ_two_yonedaEquiv_symm _

lemma long : stdSimplex.δ (1 : Fin 3) ≫ SSet.yonedaEquiv.symm C.triangle.simplex =
    SSet.yonedaEquiv.symm V.edge := SSet.Edge.CompStruct.δ_one_yonedaEquiv_symm _

lemma last : stdSimplex.δ (0 : Fin 3) ≫ SSet.yonedaEquiv.symm C.triangle.simplex =
    SSet.yonedaEquiv.symm C.edge.edge := SSet.Edge.CompStruct.δ_zero_yonedaEquiv_symm _

end TriangleDifference

variable {Y Y' : OmegaSpectrum.{u}}
  (p : X ⟶ Y) (q : Y' ⟶ Z) (a : X ⟶ Y') (b : Y ⟶ Z) (d : X ⟶ Z)
  (U V : Sp.{u} _⦋2⦌)
  (hu₂ : Sp.δ 2 U = (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge a).edge)
  (hu₀ : Sp.δ 0 U = (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge q).edge)
  (hu₁ : Sp.δ 1 U = (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge d).edge)
  (hv₂ : Sp.δ 2 V = (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge p).edge)
  (hv₀ : Sp.δ 0 V = (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge b).edge)
  (hv₁ : Sp.δ 1 V = (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge d).edge)

def squareDifference : TriangleDifference (triangleEdge a q d U hu₂ hu₀ hu₁)
    (triangleEdge p b d V hv₂ hv₀ hv₁) :=
  triangleDifference _ _

end SerrePositivity.KST.LocalizingInvariants.SpectrumMappingPrism
