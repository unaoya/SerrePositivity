module

public import SerrePositivity.KST.LocalizingInvariants.CompositionTriangleRelativePrism
public import SerrePositivity.KST.Spectra.CoherentNerve

/-!
概要：元の Sp 二単体を、元の二辺の厳密合成三角形へ相対 prism で比較する。
方針：同じ二辺の合成対応の fiber 内で両端を指定して充填する。
規約：元の二単体と固定した二辺を保持。使われ方：元の右辺二三角形の比較。
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
namespace SerrePositivity.KST.LocalizingInvariants.SpectrumTriangleNormalization

local instance nativeTriangleCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

local instance nativeTriangleNerve : Quasicategory (SimplicialNerve OmegaSpectrum.{u}) :=
  sp_quasicategory

variable {X Y Z : OmegaSpectrum.{u}} (a : X ⟶ Y) (q : Y ⟶ Z) (s : Sp.{u} _⦋2⦌)
  (h₂ : Sp.δ 2 s = (coherentNerveEdge a).edge)
  (h₀ : Sp.δ 0 s = (coherentNerveEdge q).edge)

def canonical := (coherentNerveCompStruct a q).simplex

def comparison := TriangleComparison.comparison (coherentNerveEdge a) (coherentNerveEdge q)
  s (canonical a q) h₂ h₀ (coherentNerveCompStruct a q).d₂ (coherentNerveCompStruct a q).d₀

def prism : (Δ[2] : SSet.{u + 1}) ⊗ Δ[1] ⟶ Sp.{u} :=
  TriangleComparison.prism (coherentNerveEdge a) (coherentNerveEdge q)
    s (canonical a q) h₂ h₀ (coherentNerveCompStruct a q).d₂ (coherentNerveCompStruct a q).d₀

lemma prism_zero : (Δ[2] ◁ stdSimplex.δ (1 : Fin 2)) ≫ prism a q s h₂ h₀ =
    TriangleVertex.family s := TriangleComparison.prism_zero _ _ _ _ _ _ _ _

lemma prism_one : (Δ[2] ◁ stdSimplex.δ (0 : Fin 2)) ≫ prism a q s h₂ h₀ =
    TriangleVertex.family (canonical a q) := TriangleComparison.prism_one _ _ _ _ _ _ _ _

lemma prism_first : (stdSimplex.δ (2 : Fin 3) ▷ (Δ[1] : SSet.{u + 1})) ≫
    prism a q s h₂ h₀ = fst (Δ[1] : SSet.{u + 1}) Δ[1] ≫
      SSet.yonedaEquiv.symm (coherentNerveEdge a).edge :=
  TriangleComparison.prism_first _ _ _ _ _ _ _ _

lemma prism_last : (stdSimplex.δ (0 : Fin 3) ▷ (Δ[1] : SSet.{u + 1})) ≫
    prism a q s h₂ h₀ = fst (Δ[1] : SSet.{u + 1}) Δ[1] ≫
      SSet.yonedaEquiv.symm (coherentNerveEdge q).edge :=
  TriangleComparison.prism_last _ _ _ _ _ _ _ _

variable (d : X ⟶ Z) (h₁ : Sp.δ 1 s = (coherentNerveEdge d).edge)

def diagonalEdge : (intervalMappingSpace (coherentNerveVertex X) (coherentNerveVertex Z)).Edge
    (intervalMappingVertexOfEdge (coherentNerveEdge d))
    (intervalMappingVertexOfEdge (coherentNerveEdge (a ≫ q))) :=
  TriangleComparison.diagonalEdge (coherentNerveEdge a) (coherentNerveEdge q)
    s (canonical a q) h₂ h₀ (coherentNerveCompStruct a q).d₂ (coherentNerveCompStruct a q).d₀
    (coherentNerveEdge d) (coherentNerveEdge (a ≫ q)) h₁ (coherentNerveCompStruct a q).d₁

lemma prism_diagonal : (stdSimplex.δ (1 : Fin 3) ▷ (Δ[1] : SSet.{u + 1})) ≫
    prism a q s h₂ h₀ =
      intervalMappingUncurry (SSet.yonedaEquiv.symm (diagonalEdge a q s h₂ h₀ d h₁).edge) :=
  TriangleComparison.prism_diagonal _ _ _ _ _ _ _ _ _ _ _ _

end SerrePositivity.KST.LocalizingInvariants.SpectrumTriangleNormalization
