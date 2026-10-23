module

public import SerrePositivity.KST.LocalizingInvariants.SpectrumMappingIntervalPath
public import SerrePositivity.InfinityCategories.F1.Coherent.CompositionDiagonal
public import SerrePositivity.InfinityCategories.F1.Coherent.OrderDiagrams

/-!
概要：BF 区間と後合成を、同じ合成三角形の全区間族で結ぶ。
方針：固定第二射の coherent 合成対応を使い、第一辺と対角を同じ写像空間の射へ戻す。
規約：射や区間を選び直さない。使われ方：置換単位の相対区間と右辺 prism の照合。
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

local instance postPrismCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

variable {X Y Z : OmegaSpectrum.{u}} (p : Y ⟶ Z)

lemma fixedParameter_post : coherentCompositionFixedParameter X Y Z p ≫
    coherentHomComposition X Y Z =
      (SSet.uliftFunctor.{u + 1, u}).map (SpectrumMappingAcyclic.post X p) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨s⟩
  apply ULift.ext
  change (eComp SSet X Y Z).app _
    (s, PinchedHom.constant (SimplicialCategory.homEquiv' Y Z p) n) =
      (eComp SSet X Y Z).app _ (s, (eHomEquiv SSet p).app _ PUnit.unit)
  rw [unitHom_app_constant]
  rfl

variable {f g : X ⟶ Y} (e : (mappingSpace X Y).Edge (vertexOfHom f) (vertexOfHom g))

def liftedEdge : ((SSet.uliftFunctor.{u + 1, u}).obj (mappingSpace X Y)).Edge
    (ULift.up (vertexOfHom f)) (ULift.up (vertexOfHom g)) :=
  SSet.Edge.ofTruncated (uliftTruncatedEdge e.toTruncated)

def postEdge : (mappingSpace X Z).Edge (vertexOfHom (f ≫ p)) (vertexOfHom (g ≫ p)) :=
  (e.map (SpectrumMappingAcyclic.post X p)).ofEq
    (SpectrumMappingAcyclic.post_vertex f p) (SpectrumMappingAcyclic.post_vertex g p)

def postTriangleEdge :=
  (liftedEdge e).map (coherentCompositionCorrespondence X Y Z p)

lemma postTriangleEdge_first :
    (compositionCorrespondenceFirst (coherentNerveVertex X) (coherentNerveEdge p)).app
        (Opposite.op ⦋1⦌) (postTriangleEdge p e).edge = (intervalEdge e).edge := by
  have h := congrArg (fun k ↦ k.app (Opposite.op ⦋1⦌) (liftedEdge e).edge)
    (coherentCompositionCorrespondence_first X Y Z p)
  exact h

lemma postTriangleEdge_diagonal :
    (compositionCorrespondenceDiagonal (coherentNerveVertex X) (coherentNerveEdge p)).app
        (Opposite.op ⦋1⦌) (postTriangleEdge p e).edge = (intervalEdge (postEdge p e)).edge := by
  have hc : coherentCompositionCorrespondence X Y Z p ≫
      compositionCorrespondenceDiagonal (coherentNerveVertex X) (coherentNerveEdge p) =
    (SSet.uliftFunctor.{u + 1, u}).map (SpectrumMappingAcyclic.post X p) ≫
      coherentHomIntervalComparison X Z := by
    rw [coherentCompositionCorrespondence_diagonal, ← Category.assoc, fixedParameter_post]
  exact congrArg (fun k ↦ k.app (Opposite.op ⦋1⦌) (liftedEdge e).edge) hc

lemma postTriangleEdge_diagonal_constant (k : X ⟶ Z)
    (h : (SpectrumMappingAcyclic.post X p).app (Opposite.op ⦋1⦌) e.edge =
      PinchedHom.constant (vertexOfHom k) 1) :
    (compositionCorrespondenceDiagonal (coherentNerveVertex X) (coherentNerveEdge p)).app
        (Opposite.op ⦋1⦌) (postTriangleEdge p e).edge =
      PinchedHom.constant (intervalMappingVertexOfEdge (coherentNerveEdge k)) 1 := by
  have he := h.trans (pinchedConstant_one _)
  have hp := congrArg (fun z ↦ (coherentHomIntervalComparison X Z).app
    (Opposite.op ⦋1⦌) (ULift.up z)) he
  have hn := SSet.σ_naturality_apply (coherentHomIntervalComparison X Z) 0
    (ULift.up (vertexOfHom k))
  have hv := congrArg (fun z ↦ (intervalMappingSpace
    (coherentNerveVertex X) (coherentNerveVertex Z)).σ 0 z) (interval_vertex k)
  have ht : (intervalMappingSpace (coherentNerveVertex X) (coherentNerveVertex Z)).σ 0
      (intervalMappingVertexOfEdge (coherentNerveEdge k)) =
    PinchedHom.constant (intervalMappingVertexOfEdge (coherentNerveEdge k)) 1 :=
      (pinchedConstant_one (X := intervalMappingSpace
        (coherentNerveVertex X) (coherentNerveVertex Z))
          (intervalMappingVertexOfEdge (coherentNerveEdge k))).symm
  exact (postTriangleEdge_diagonal p e).trans
    (hp.trans (hn.trans (hv.trans ht)))

end SerrePositivity.KST.LocalizingInvariants.SpectrumMappingPath
