module
public import SerrePositivity.KST.Fibration.KanClosedEvaluation
public import SerrePositivity.InfinityCategories.F1.KanAnodyneLocalization
public import SerrePositivity.InfinityCategories.HomotopyLimits.SpaceTerminal
public import SerrePositivity.InfinityCategories.F1.CoherentKanInvertible
public import SerrePositivity.KST.Comparison.ExInfinityLocalization

/-! # 元の一点射の可逆性から、同じ Ex∞ 値の空間の ∞ 圏での終対象性へ接続する -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.InfinityCategories.HomotopyLimits
open SerrePositivity.KST.SConstruction
open SerrePositivity.KST.Comparison
open SerrePositivity.SimplicialModel
namespace SerrePositivity.KST.Fibration

/-- 元の Kan 値の一点射が可逆なら、同じ元の空間の頂点は終対象である。 -/
theorem kanVertex_isTerminal_of_localized_toPoint (K : KanObject.{u})
    (hK : IsIso (AnodyneHomotopy.anodyneQ.map (terminal.from K.obj))) :
    IsTerminalVertex (coherentNerveVertex K) := by
  let Q := AnodyneHomotopy.anodyneQ.{u}
  let f : K ⟶ pointKanObject.{u} := stdSimplex.isTerminalObj₀.from K.obj
  have hp : IsIso (terminal.from pointKanObject.{u}.obj) :=
    isIso_of_isTerminal stdSimplex.isTerminalObj₀ terminalIsTerminal _
  have he : (show K.obj ⟶ pointKanObject.{u}.obj from f) ≫
      terminal.from pointKanObject.{u}.obj = terminal.from K.obj := terminal.hom_ext _ _
  have hf : IsIso (Q.map (show K.obj ⟶ pointKanObject.{u}.obj from f)) := by
    have hc : IsIso (Q.map (show K.obj ⟶ pointKanObject.{u}.obj from f) ≫
        Q.map (terminal.from pointKanObject.{u}.obj)) := by
      rw [← Functor.map_comp, he]
      exact hK
    exact (isIso_comp_right_iff _ _).mp hc
  have hi : IsInvertibleEdge (coherentNerveEdge f) :=
    coherentKanEdge_isInvertible_of_isQCatEquivalence (K := K) (L := pointKanObject.{u})
      (isQCatEquivalence_of_anodyneQ_isIso (show K.obj ⟶ pointKanObject.{u}.obj from f) hf)
  have : IsIso (Truncated.HomotopyCategory.homMk (coherentNerveEdge f).toTruncated) := hi
  have ht : IsTerminalVertex (coherentNerveVertex pointKanObject.{u}) := by
    simpa only [pointSpaceVertex, spaceInfinityVertex_eq_coherent] using
      pointSpaceVertex_isTerminalVertex.{u}
  exact ht.of_vertexIso (asIso
    (Truncated.HomotopyCategory.homMk (coherentNerveEdge f).toTruncated)).symm

/-- 元の一点射が可逆な実現の、同じ Ex∞ Kan 値は空間の ∞ 圏の終対象である。 -/
theorem exInfinityVertex_isTerminal_of_localized_toPoint (V : SSet.{u})
    (hV : IsIso (AnodyneHomotopy.anodyneQ.map (terminal.from V))) :
    IsTerminalVertex (coherentNerveVertex (exInfinityClosedKanEnrichedFunctor.obj ⟨V⟩)) := by
  apply kanVertex_isTerminal_of_localized_toPoint
  let Q := AnodyneHomotopy.anodyneQ.{u}
  have hu : IsIso (Q.map (exInfinityUnit.app V)) := inferInstance
  have he : exInfinityUnit.app V ≫ terminal.from (exInfinity.obj V) =
      terminal.from V := terminal.hom_ext _ _
  have hc : IsIso (Q.map (exInfinityUnit.app V) ≫
      Q.map (terminal.from (exInfinity.obj V))) := by
    rw [← Functor.map_comp, he]
    exact hV
  exact (isIso_comp_left_iff _ _).mp hc

end SerrePositivity.KST.Fibration
