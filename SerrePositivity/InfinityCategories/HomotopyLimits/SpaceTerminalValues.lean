module

public import SerrePositivity.InfinityCategories.HomotopyLimits.SpaceTerminal
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.PointedSpaceMappingSpaces
public import SerrePositivity.InfinityCategories.F1.Coherent.KanInvertible
public import SerrePositivity.InfinityCategories.F1B.Homotopy.WeakContractibleKan
public import SerrePositivity.InfinityCategories.Stable.UniverseZeroObjects

/-!
概要：空間の ∞ 圏の終対象性を、元の Kan 値の可縮性と照合する。
方針：一点への元の射の可逆性と、一点からの元の写像空間比較を両方向に使う。
規約：任意の SpaceInfinity の頂点と、その元の値を保持する。
使われ方：P_Σ の空積条件と、元の表現可能前層への適用。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 元の Kan 対象が可縮なら、その元の空間の頂点は終対象。 -/
lemma spaceInfinityVertex_isTerminal_of_isContractibleKan (K : KanObject.{u})
    (hK : IsContractibleKan K.obj) : IsTerminalVertex (spaceInfinityVertex K) := by
  let f : K ⟶ pointKanObject.{u} := stdSimplex.isTerminalObj₀.from K.obj
  have hpt : IsContractibleKan pointKanObject.{u}.obj := by
    intro n a
    exact ⟨stdSimplex.isTerminalObj₀.from _, stdSimplex.isTerminalObj₀.hom_ext _ _⟩
  have hc : IsWeakHomotopyEquivalence
      ((show K.obj ⟶ pointKanObject.{u}.obj from f) ≫ terminal.from pointKanObject.{u}.obj) := by
    rw [show (show K.obj ⟶ pointKanObject.{u}.obj from f) ≫
      terminal.from pointKanObject.{u}.obj = terminal.from K.obj from
      terminal.hom_ext _ _]
    exact hK.isWeaklyContractible
  have hf := (hpt.isWeaklyContractible.cancel_right hc).isSimplicialHomotopyEquivalence
  have hi := coherentKanEdge_isInvertible_of_isQCatEquivalence hf.isQCatEquivalence
  have : IsIso (Truncated.HomotopyCategory.homMk (coherentNerveEdge f).toTruncated) := hi
  let e := asIso (Truncated.HomotopyCategory.homMk (coherentNerveEdge f).toTruncated)
  have ht : IsTerminalVertex (coherentNerveVertex pointKanObject.{u}) := by
    simpa only [pointSpaceVertex, spaceInfinityVertex_eq_coherent] using
      pointSpaceVertex_isTerminalVertex.{u}
  simpa only [spaceInfinityVertex_eq_coherent] using ht.of_vertexIso e.symm

/-- 空間の元の頂点は、その元の Kan 値が可縮であることと同値に終対象。 -/
lemma spaceInfinity_isTerminal_iff_value_isContractibleKan (s : SpaceInfinity.{u} _⦋0⦌) :
    IsTerminalVertex s ↔ IsContractibleKan (spaceInfinityObject s).obj := by
  constructor
  · intro hs
    have h := (pointSpaceRightMappingEquivalenceAt s).isContractibleKan
      (hs.pinchedHom_isContractibleKan pointSpaceVertex)
    apply isContractibleKan_of_nonempty_of_all_terminal
    · obtain ⟨x⟩ := h.nonempty
      exact ⟨x.down⟩
    · intro x
      exact (isTerminalVertex_iff_ulift x).mpr (h.isTerminalVertex (ULift.up x))
  · intro hs
    have hv : spaceInfinityVertex (spaceInfinityObject s) = s :=
      spaceInfinityVertexEquiv.apply_symm_apply s
    exact hv ▸ spaceInfinityVertex_isTerminal_of_isContractibleKan _ hs

end SerrePositivity.InfinityCategories.HomotopyLimits
