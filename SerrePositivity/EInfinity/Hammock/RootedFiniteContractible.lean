module

public import SerrePositivity.EInfinity.Hammock.RootedFiniteHammockColimit
public import SerrePositivity.EInfinity.Hammock.WeakFiniteSubsetColimit
public import SerrePositivity.EInfinity.Hammock.QuiverTreeFiniteContractible

/-!
# 根付き木の全体の元の hammock の弱可縮性

概要：有限包の実際の hammock の可縮性を全体へ移す。
方針：有限部分集合の filtered 余極限と全語の余極限の交換を使う。
規約：元の全端点と全語の hammock を保持する。
使われ方：自由被覆の評価の fiber の可縮性。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.RootedFinite
open CategoryTheory Limits SerrePositivity.InfinityCategories
attribute [local instance] Classical.propDecidable

variable {Q : Type u} [Quiver.{v} Q] (T : WideSubquiver (Quiver.Symmetrify Q))
  [Quiver.Arborescence T] [Quiver.IsThin (Quiver.FreeGroupoid Q)] (X Y : Q)

lemma hammockDiagram_obj_isWeaklyContractible (S : Finset Q) :
    IsWeaklyContractible ((hammockDiagram T X Y).obj S) := by
  let := FiniteQuiver.quiver (hull T X Y S)
  change IsWeaklyContractible (colimit ((graphWordDiagram T X Y).flip.obj S))
  rw [wordDiagram_eq]
  exact QuiverTree.finite_colimit_isWeaklyContractible T (hull T X Y S)
    (QuiverTree.endpointHull_closed T X Y S) (left T X Y S) (right T X Y S)

include T in
lemma colimit_isWeaklyContractible :
    IsWeaklyContractible (colimitGraph (⊤ : MorphismProperty (Paths Q))
      ((Paths.of Q).obj X) ((Paths.of Q).obj Y)) := by
  have h := finiteSubsetColimit_isWeaklyContractible (hammockDiagram T X Y)
    (hammockDiagram_obj_isWeaklyContractible T X Y)
  let e := hammockColimitIso T X Y
  have he := (isPrecompositionEquivalence_of_iso e).isWeakHomotopyEquivalence
  have ht : e.hom ≫ terminal.from _ = terminal.from _ := terminal.hom_ext _ _
  apply he.cancel_left
  rw [ht]
  exact h

end SerrePositivity.EInfinity.Hammock.RootedFinite
