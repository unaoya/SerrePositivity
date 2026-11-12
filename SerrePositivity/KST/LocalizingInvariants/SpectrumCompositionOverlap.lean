module

public import SerrePositivity.KST.LocalizingInvariants.CoherentCompositionTetrahedron
public import SerrePositivity.KST.LocalizingInvariants.CompositionOverlapHomotopy
public import SerrePositivity.KST.LocalizingInvariants.SpectrumTriangleCommutation
public import SerrePositivity.KST.LocalizingInvariants.HomotopyMapTransport

/-!
概要：BF の三つの射の標準三角形に対し、辺比較の二通りの合成を同定する。
方針：通常の nerve の三単体を使い、四面の全射の一致を格子の合成式へ渡す。
規約：結合律の端点輸送も明示する。使われ方：置換単位を含む模型右辺の貼合せ。
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

local instance overlapCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

local instance overlapNerve : Quasicategory (SimplicialNerve OmegaSpectrum.{u}) :=
  sp_quasicategory

variable {A B C D : OmegaSpectrum.{u}} (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ D)

def associatedPre : SSet.Homotopy
    (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge ((a ≫ b) ≫ c)).edge)
    (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (b ≫ c)).edge) :=
  HomotopyArrow.rebase (canonicalPre a (b ≫ c))
    (congrArg (fun f ↦ SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f).edge)
      (Category.assoc a b c).symm) rfl

lemma canonicalPre_tetrahedron : (canonicalPre a b).h =
    SquareDiagonal.preShape ≫ stdSimplex.δ (3 : Fin 4) ≫
      SSet.yonedaEquiv.symm (CoherentComposition.tetrahedron a b c) := by
  rw [CoherentComposition.face_map a b c (CoherentComposition.face_last a b c)]
  rfl

lemma canonicalPost_tetrahedron : (canonicalPost b c).h =
    SquareDiagonal.postShape ≫ stdSimplex.δ (0 : Fin 4) ≫
      SSet.yonedaEquiv.symm (CoherentComposition.tetrahedron a b c) := by
  rw [CoherentComposition.face_map a b c (CoherentComposition.face_first a b c)]
  rfl

def overlapLong := CompositionOverlap.longHomotopy
  (SSet.yonedaEquiv.symm (CoherentComposition.tetrahedron a b c))
  (canonicalPre a b) (canonicalPost b c)
  (canonicalPre_tetrahedron a b c) (canonicalPost_tetrahedron a b c)

lemma overlapLong_afterBottom :
    Arrow.mk (Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
      (SquareDiagonal.afterBottom (overlapLong a b c)))) =
    Arrow.mk (Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (canonicalPost (a ≫ b) c))) := by
  apply HomotopyArrow.congr
  rw [overlapLong, CompositionOverlap.afterBottom_map,
    CoherentComposition.face_map a b c (CoherentComposition.face_lower a b c)]
  rfl

lemma overlapLong_beforeTop :
    Arrow.mk (Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
      (SquareDiagonal.beforeTop (overlapLong a b c)))) =
    Arrow.mk (Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (associatedPre a b c))) := by
  apply HomotopyArrow.congr
  rw [associatedPre, HomotopyArrow.rebase_map, overlapLong,
    CompositionOverlap.beforeTop_map,
    CoherentComposition.face_map a b c (CoherentComposition.face_upper a b c)]
  rfl

lemma canonical_overlap :
    Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (canonicalPre a b)) ≫
        Truncated.HomotopyCategory.homMk
          (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (canonicalPost b c)) =
    Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (canonicalPost (a ≫ b) c)) ≫
        Truncated.HomotopyCategory.homMk
          (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (associatedPre a b c)) := by
  have he := CompositionOverlap.homMk_overlap
    (SSet.yonedaEquiv.symm (CoherentComposition.tetrahedron a b c))
    (canonicalPre a b) (canonicalPost b c)
    (canonicalPre_tetrahedron a b c) (canonicalPost_tetrahedron a b c)
  apply Arrow.mk_injective
  exact (congrArg Arrow.mk he).trans
    (arrow_mk_comp_congr (overlapLong_afterBottom a b c) (overlapLong_beforeTop a b c))

end SerrePositivity.KST.LocalizingInvariants.SpectrumTriangleNormalization
