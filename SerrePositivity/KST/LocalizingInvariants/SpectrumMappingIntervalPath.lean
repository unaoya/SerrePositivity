module

public import SerrePositivity.KST.Spectra.SpectrumWhiteheadEquivalence
public import SerrePositivity.KST.Spectra.CoherentNerve
public import SerrePositivity.InfinityCategories.F1.Coherent.HomIntervalVertices
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.IntervalMappingFaceEndpoints
public import SerrePositivity.InfinityCategories.F1B.Homotopy.HomotopyRepresentative

/-!
概要：BF 写像空間の指定区間を、両端の対象を固定した Sp の辺の全族へ送る。
方針：coherent 区間 Hom 比較を同じ一単体へ適用し、区間模型を内部 Hom へ含める。
規約：π₀ の一致から族を選び直さない。使われ方：置換単位と指定 prism の全図式比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Spectra
open OmegaSpectrum
namespace SerrePositivity.KST.LocalizingInvariants.SpectrumMappingPath

local instance intervalPathCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory
local instance intervalPathNerve : Quasicategory (SimplicialNerve OmegaSpectrum.{u}) :=
  sp_quasicategory

variable {X Y : OmegaSpectrum.{u}} {f g : X ⟶ Y}
  (e : (mappingSpace X Y).Edge (vertexOfHom f) (vertexOfHom g))

lemma interval_vertex (k : X ⟶ Y) :
    (coherentHomIntervalComparison X Y).app (Opposite.op ⦋0⦌) (ULift.up (vertexOfHom k)) =
      intervalMappingVertexOfEdge (coherentNerveEdge k) := by
  rw [← SpectrumMappingAcyclic.homEquiv'_eq_vertex, coherentHomIntervalComparison_vertex,
    Equiv.symm_apply_apply]

def intervalEdge : (intervalMappingSpace (coherentNerveVertex X) (coherentNerveVertex Y)).Edge
    (intervalMappingVertexOfEdge (coherentNerveEdge f))
    (intervalMappingVertexOfEdge (coherentNerveEdge g)) :=
  ((SSet.Edge.ofTruncated (X := (SSet.uliftFunctor.{u + 1, u}).obj (mappingSpace X Y))
    (uliftTruncatedEdge e.toTruncated)).map (coherentHomIntervalComparison X Y)).ofEq
      (interval_vertex f) (interval_vertex g)

lemma intervalEdge_simplex : (intervalEdge e).edge =
    (coherentHomIntervalComparison X Y).app (Opposite.op ⦋1⦌) (ULift.up e.edge) := rfl

def arrowEdge : ((ihom (Δ[1] : SSet.{u + 1})).obj Sp.{u}).Edge
    (functorVertex (SSet.yonedaEquiv.symm (coherentNerveEdge f).edge))
    (functorVertex (SSet.yonedaEquiv.symm (coherentNerveEdge g).edge)) :=
  (intervalEdge e).map (vertexFiberι _ _)

def homotopy : SSet.Homotopy
    (SSet.yonedaEquiv.symm (coherentNerveEdge f).edge)
    (SSet.yonedaEquiv.symm (coherentNerveEdge g).edge) :=
  simplicialHomotopyOfFunctorEdge (arrowEdge e).toTruncated

lemma arrowEdge_isInvertible : IsInvertibleEdge (arrowEdge e).toTruncated := by
  have hi : IsInvertibleEdge (intervalEdge e).toTruncated :=
    IsGroupoid.all_isIso (C := hoFunctor.obj
      (intervalMappingSpace (coherentNerveVertex X) (coherentNerveVertex Y))) _
  exact hi.map (vertexFiberι _ _)

def arrowIso : FunctorIso (SSet.yonedaEquiv.symm (coherentNerveEdge f).edge)
    (SSet.yonedaEquiv.symm (coherentNerveEdge g).edge) := by
  have := arrowEdge_isInvertible e
  exact asIso (Truncated.HomotopyCategory.homMk (arrowEdge e).toTruncated)

lemma homotopy_map : (homotopy e).h =
    intervalMappingUncurry (SSet.yonedaEquiv.symm (intervalEdge e).edge) := by
  unfold intervalMappingUncurry
  rw [SSet.yonedaEquiv_symm_comp]
  rfl

lemma homotopy_source :
    (stdSimplex.δ (1 : Fin 2) ▷ (Δ[1] : SSet.{u + 1})) ≫ (homotopy e).h =
      fst (Δ[0] : SSet.{u + 1}) Δ[1] ≫ SSet.yonedaEquiv.symm (coherentNerveVertex X) := by
  rw [homotopy_map]
  exact intervalMappingUncurry_face_source _

lemma homotopy_target :
    (stdSimplex.δ (0 : Fin 2) ▷ (Δ[1] : SSet.{u + 1})) ≫ (homotopy e).h =
      fst (Δ[0] : SSet.{u + 1}) Δ[1] ≫ SSet.yonedaEquiv.symm (coherentNerveVertex Y) := by
  rw [homotopy_map]
  exact intervalMappingUncurry_face_target _

end SerrePositivity.KST.LocalizingInvariants.SpectrumMappingPath
