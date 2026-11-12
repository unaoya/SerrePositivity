module

public import SerrePositivity.KST.NonConnective.SequentialColimit
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ColimitVertexTransport
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.StrictCoconeLegs

/-!
概要：既存 filteredOmegaSpectrum と同じ BF 候補を頂点とする実 Sp 余極限余錐。
方針：元の比較射そのものを coslice の可逆辺として終点から持ち上げる。
規約：余極限性に加え、比較の射影の一次単体の厳密な等式を保持する。
使われ方：既存の整数 π 比較と実際の余極限余錐の脚の照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.NonConnective
local instance sequentialCandidateSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory
local instance sequentialCandidateHomKan (X Y : OmegaSpectrum.{u}) :
    KanComplex (SimplicialCategory.sHom X Y) := OmegaSpectrum.mappingSpace_kanComplex X Y

/-- 同じ候補頂点・実余錐・実比較辺と、その全ての検証済み条件。 -/
structure SequentialCandidateColimitData (D : SpectrumSequence.{u}) where
  /-- 元の図式上の実余錐。 -/
  cocone : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram D)
  /-- 同じ余錐の ∞ 普遍性。 -/
  isColimit : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone cocone
  /-- 既存の BF 候補を厳密に頂点とする。 -/
  vertex : cocone.vertex = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (sequentialSpectrum D)
  /-- 元の段ごとの余錐への、coslice 内の実際の比較辺。 -/
  comparison : SSet.Truncated.Edge
    (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram D)))
      cocone (sequentialSpColimitCocone D)
  /-- その頂点辺は、元の BF 射影そのもの。 -/
  comparison_edge :
    (comparison.map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram D)))).edge =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (sequentialReplacementProjection D)).edge

/-- 元の可逆な BF 射影を、元の余極限余錐へ終点を保って実際に持ち上げる。 -/
lemma sequentialCandidateColimitData_nonempty (D : SpectrumSequence.{u}) :
    Nonempty (SequentialCandidateColimitData D) := by
  let c := sequentialSpColimitCocone D
  let q := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram D)
  let p := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (sequentialReplacementProjection D)
  let e : SSet.Truncated.Edge (X := (truncation 2).obj (SimplicialNerve OmegaSpectrum))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (sequentialSpectrum D)) (q.app (Opposite.op ⦋0⦌) c) :=
    ⟨p.edge, p.src_eq, p.tgt_eq.trans (sequentialSpColimitCocone_vertex D).symm⟩
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge e := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (e := p.toTruncated)
    (f := e) rfl).mp (OmegaSpectrum.isInvertible_of_piIsomorphism _
      (sequentialReplacementProjection_piIsomorphism D))
  obtain ⟨F, hF₀, hFq⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.leftFibration_liftInvertibleEdge_target q c e he
  let s := SSet.yonedaEquiv F
  let d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram D) := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder _).δ 1 s
  have hs : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder _).δ 0 s = c := by
    rw [← stdSimplex.yonedaEquiv_δ_comp, hF₀, Equiv.apply_symm_apply]
  let a : SSet.Truncated.Edge (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram D)))
      d c := ⟨s, rfl, hs⟩
  have hm : (a.map ((truncation 2).map q)).edge = p.edge := by
    change q.app (Opposite.op ⦋1⦌) (SSet.yonedaEquiv F) = _
    rw [← SSet.yonedaEquiv_comp, hFq]
    exact Equiv.apply_symm_apply _ e.edge
  have ha := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.leftFibration_reflects_invertibleEdge q a
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr hm).mpr
      (OmegaSpectrum.isInvertible_of_piIsomorphism _
        (sequentialReplacementProjection_piIsomorphism D)))
  let : IsIso (SSet.Truncated.HomotopyCategory.homMk a) := ha
  refine ⟨⟨d, (sequentialSpColimitCocone_isColimit D).of_vertexIso
    (asIso (SSet.Truncated.HomotopyCategory.homMk a)).symm, ?_, a, hm⟩⟩
  have ht := congrArg (fun z ↦ (SimplicialNerve OmegaSpectrum).δ 1 z) hm
  have hn := ConcreteCategory.congr_hom
    (q.naturality (SimplexCategory.δ (1 : Fin 2)).op) s
  exact hn.trans (ht.trans p.src_eq)

/-- 同じ BF 候補を頂点とし、元の BF 射影を保持した実余極限データ。 -/
def sequentialCandidateColimitData (D : SpectrumSequence.{u}) : SequentialCandidateColimitData D :=
  Classical.choice (sequentialCandidateColimitData_nonempty D)

/-- 既存の BF 候補を頂点とする、元の図式上の実際の Sp 余極限余錐。 -/
def sequentialCandidateColimitCocone (D : SpectrumSequence.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram D) := (sequentialCandidateColimitData D).cocone

/-- 同じ実余錐の追加仮定なしの ∞ 余極限性。 -/
theorem sequentialCandidateColimitCocone_isColimit (D : SpectrumSequence.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (sequentialCandidateColimitCocone D) :=
  (sequentialCandidateColimitData D).isColimit

/-- 同じ実余錐の頂点は、既存 filteredOmegaSpectrum の BF 候補。 -/
lemma sequentialCandidateColimitCocone_vertex (D : SpectrumSequence.{u}) :
    (sequentialCandidateColimitCocone D).vertex = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (sequentialSpectrum D) :=
  (sequentialCandidateColimitData D).vertex

end SerrePositivity.KST.NonConnective
