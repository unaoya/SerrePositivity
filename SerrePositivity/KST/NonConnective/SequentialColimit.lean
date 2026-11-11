module

public import SerrePositivity.KST.NonConnective.SequentialConeComparison
public import SerrePositivity.KST.NonConnective.SequentialLevelColimitMap

/-!
概要：任意の元の逐次 BF 列の、段ごとの実 Sp 余錐と ∞ 余極限性。
方針：相対 cofibrant な列の Hom 塔で証明した普遍性を、余錐全体の実同型で輸送する。
規約：元の列と元の各脚を保持し、余極限性を仮定入力にしない。
使われ方：K-7 工程 1 の実際の逐次 Sp 余極限。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.NonConnective
local instance sequentialColimitSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory
local instance sequentialColimitHomKan (X Y : OmegaSpectrum.{u}) :
    KanComplex (SimplicialCategory.sHom X Y) := OmegaSpectrum.mappingSpace_kanComplex X Y
local instance sequentialColimitOppositeHomKan (X Y : OmegaSpectrum.{u}ᵒᵖ) :
    KanComplex (SimplicialCategory.sHom X Y) :=
  OmegaSpectrum.mappingSpace_kanComplex Y.unop X.unop

/-- BF 射の可逆性は、同じ通常射の反対の coherent 辺にも保たれる。 -/
lemma sequentialOppositeEdge_isInvertible {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f.op) := by
  have h := hf.op.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentNerveOppositeMap OmegaSpectrum)
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentNerveOppositeMap_edge f)).mp h

/-- 元の任意の逐次 BF 列の、元の段ごとの厳密な余錐は Sp の ∞ 余極限。 -/
theorem sequentialLevelColimitCocone_isColimit (D : SpectrumSequence.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.strictNativeCocone (sequentialLevelColimitCocone D)) := by
  let R := sequentialDiagramReplacement D
  let η := sequentialDiagramReplacementComparison D
  let m := sequentialLevelColimitMap η
  have hR : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone (sequentialLevelColimitCocone R).op) :=
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.strictNativeCocone_isColimit_iff _).mp (sequentialReplacementLevelCocone_isColimit D)
  have e := sequentialConeFunctorIso (sequentialLevelColimitCocone D).op
    (sequentialLevelColimitCocone R).op (NatTrans.op η) m.op (by
      intro a
      apply Quiver.Hom.unop_inj
      exact sequentialLevelColimitMap_fac η a.unop) (by
      intro a
      exact sequentialOppositeEdge_isInvertible _
        (OmegaSpectrum.isInvertible_of_piIsomorphism _
          (sequentialDiagramReplacementComparison_piIsomorphism D a.unop)))
    (sequentialOppositeEdge_isInvertible m
      (OmegaSpectrum.isInvertible_of_piIsomorphism m
        (sequentialLevelColimitMap_piIsomorphism η
          (sequentialDiagramReplacementComparison_piIsomorphism D))))
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.strictNativeCocone_isColimit_iff]
  exact hR.of_functorIso e.symm

/-- 元の任意の逐次 BF 列上の、元の段ごとの注入を持つ実 Sp 余錐。 -/
def sequentialSpColimitCocone (D : SpectrumSequence.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram D) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.strictNativeCocone (sequentialLevelColimitCocone D)

/-- 同じ実 Sp 余錐の、追加仮定なしの ∞ 余極限性。 -/
theorem sequentialSpColimitCocone_isColimit (D : SpectrumSequence.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (sequentialSpColimitCocone D) := sequentialLevelColimitCocone_isColimit D

/-- 同じ実余極限余錐の頂点は、元の段ごとの BF 余極限そのもの。 -/
lemma sequentialSpColimitCocone_vertex (D : SpectrumSequence.{u}) :
    (sequentialSpColimitCocone D).vertex = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (sequentialLevelColimitSpectrum D) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.strictNativeCocone_vertex _

end SerrePositivity.KST.NonConnective
