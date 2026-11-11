module

public import SerrePositivity.KST.LocalizingInvariants.CompositionPreShape
public import SerrePositivity.KST.LocalizingInvariants.HomotopyTriangleComposition
public import SerrePositivity.KST.LocalizingInvariants.SpectrumCompositionOverlap

/-!
概要：BF の三つの射の標準上側比較二つを、合成射の標準上側比較と同定する。
方針：共通終点の三辺の全三角形族を、元の coherent 三単体から構成する。
規約：結合律による始点輸送を明示。使われ方：置換単位を含む右辺の合成計算。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Spectra
open OmegaSpectrum
namespace SerrePositivity.KST.LocalizingInvariants.SpectrumTriangleNormalization

local instance preCompositionCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

variable {A B C D : OmegaSpectrum.{u}} (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ D)

def associatedLongPre := HomotopyArrow.rebase (canonicalPre (a ≫ b) c)
  (congrArg (fun f ↦ SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f).edge)
    (Category.assoc a b c)) rfl

lemma canonicalPre_comp :
    Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (canonicalPre a (b ≫ c))) ≫
        Truncated.HomotopyCategory.homMk
          (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (canonicalPre b c)) =
    Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (associatedLongPre a b c)) := by
  apply HomotopyTriangle.homMk_comp _ _ _
    (CompositionPre.shape ≫ SSet.yonedaEquiv.symm (CoherentComposition.tetrahedron a b c))
  · rw [← Category.assoc, CompositionPre.first, Category.assoc,
      CoherentComposition.face_map a b c (CoherentComposition.face_upper a b c)]
    rfl
  · rw [← Category.assoc, CompositionPre.last, Category.assoc,
      CoherentComposition.face_map a b c (CoherentComposition.face_first a b c)]
    rfl
  · rw [← Category.assoc, CompositionPre.long, Category.assoc,
      CoherentComposition.face_map a b c (CoherentComposition.face_lower a b c)]
    unfold associatedLongPre
    rw [HomotopyArrow.rebase_map]
    rfl

lemma canonicalPre_comp_arrow : Arrow.mk
    (Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (canonicalPre a (b ≫ c))) ≫
        Truncated.HomotopyCategory.homMk
          (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (canonicalPre b c))) =
    Arrow.mk (Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (canonicalPre (a ≫ b) c))) :=
  (congrArg Arrow.mk (canonicalPre_comp a b c)).trans
    (HomotopyArrow.rebase_arrow _ _ _).symm

end SerrePositivity.KST.LocalizingInvariants.SpectrumTriangleNormalization
