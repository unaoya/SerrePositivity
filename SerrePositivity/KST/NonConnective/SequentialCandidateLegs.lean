module

public import SerrePositivity.KST.NonConnective.SequentialCandidateColimit
public import SerrePositivity.KST.NonConnective.SequentialColimitPi
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoconeVertexLegNormalization

/-!
概要：同じ BF 候補の実余極限余錐の各辺と、既存の整数 π 比較に使う注入の照合。
方針：実 coslice 辺の可換三角形と元の BF 射影の厳密合成式を比較し、可逆射を消去する。
規約：各脚そのもののホモトピー圏での等号を証明する。
使われ方：実 Sp cocone と全整数 π の既存余極限比較の接続。
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
local instance sequentialCandidateLegSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory
local instance sequentialCandidateLegHomKan (X Y : OmegaSpectrum.{u}) :
    KanComplex (SimplicialCategory.sHom X Y) := OmegaSpectrum.mappingSpace_kanComplex X Y

/-- 同じ候補を頂点とする実余極限余錐の脚を、元の入力段と候補の標準頂点で読む。 -/
def sequentialCandidateColimitLeg (D : SpectrumSequence.{u}) (a : SequentialIndex.{u}) :
    (SimplicialNerve OmegaSpectrum).Edge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (D.obj a))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (sequentialSpectrum D)) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeVertexLegAt (sequentialCandidateColimitCocone D) (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex a))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (D.obj a)) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram_vertex D a)).ofEq rfl
      (sequentialCandidateColimitCocone_vertex D)

/-- 段ごとの実余極限余錐の脚の一次単体は、元の厳密 BF 注入の coherent 辺。 -/
lemma sequentialSpColimitCocone_leg_edge (D : SpectrumSequence.{u}) (a : SequentialIndex.{u}) :
    ((sequentialSpColimitCocone D).leg
      (SSet.yonedaEquiv.symm (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex a)))).edge =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (sequentialLevelColimitInjection D a)).edge := by
  have h := congrArg SSet.yonedaEquiv
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictNativeCoconeLeg_eq (sequentialLevelColimitCocone D) a)
  exact h.trans (Equiv.apply_symm_apply _ _)

/-- 元の coslice 比較の三角形は、同じ BF 候補の脚と同じ BF 射影で可換。 -/
def sequentialCandidateColimitLeg_projection_triangle (D : SpectrumSequence.{u})
    (a : SequentialIndex.{u}) :
    (sequentialCandidateColimitLeg D a).toTruncated.CompStruct
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (sequentialReplacementProjection D)).toTruncated
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (sequentialLevelColimitInjection D a)).toTruncated := by
  let t := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.legCompStruct (sequentialCandidateColimitData D).comparison
    (SSet.yonedaEquiv.symm (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex a)))
  exact ⟨t.simplex, t.d₂,
    t.d₀.trans (sequentialCandidateColimitData D).comparison_edge,
    t.d₁.trans (sequentialSpColimitCocone_leg_edge D a)⟩

/-- 実余極限余錐の各脚は、全整数 π の既存比較に使った同じ注入の辺と hSp で等しい。 -/
theorem sequentialCandidateColimitLeg_hom_eq (D : SpectrumSequence.{u})
    (a : SequentialIndex.{u}) :
    SSet.Truncated.HomotopyCategory.homMk (sequentialCandidateColimitLeg D a).toTruncated =
      SSet.Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (OmegaSpectrum.filteredSpectrumInjection D a)).toTruncated := by
  let p := SSet.Truncated.HomotopyCategory.homMk
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (sequentialReplacementProjection D)).toTruncated
  let : IsIso p := OmegaSpectrum.isInvertible_of_piIsomorphism _
    (sequentialReplacementProjection_piIsomorphism D)
  apply (cancel_mono p).mp
  have h₁ := SSet.Truncated.HomotopyCategory.homMk_comp_homMk
    (sequentialCandidateColimitLeg_projection_triangle D a)
  have h₂ := SSet.Truncated.HomotopyCategory.homMk_comp_homMk
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveCompStruct (OmegaSpectrum.filteredSpectrumInjection D a)
      (sequentialReplacementProjection D)).toTruncated
  rw [sequentialInjection_projection] at h₂
  exact h₁.trans h₂.symm

end SerrePositivity.KST.NonConnective
