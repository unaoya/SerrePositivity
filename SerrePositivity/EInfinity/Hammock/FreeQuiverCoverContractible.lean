module

public import SerrePositivity.EInfinity.Hammock.RootedFiniteContractible
public import SerrePositivity.EInfinity.Hammock.FreeQuiverCoverFiniteContractible
public import SerrePositivity.EInfinity.Hammock.FreeQuiverCoverHammockFiber

/-!
# 元の自由被覆の hammock と評価の fiber の弱可縮性

概要：元の自由被覆の全端点の hammock と元の評価の各 fiber は弱可縮となる。
方針：被覆の測地木への代入と同じ評価の fiber 同型を使う。
規約：薄さや可縮性を追加入力にしない。
使われ方：指定自由圏の評価と DK の比較。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.FreeQuiverCover
open CategoryTheory Limits SerrePositivity.InfinityCategories

variable {Q : Type u} [Quiver.{v} Q] (A : Q)

lemma colimit_isWeaklyContractible :
    letI := quiver A
    ∀ X Y : Paths (Vertex A), IsWeaklyContractible (colimitGraph
      (⊤ : MorphismProperty (Paths (Vertex A))) X Y) := by
  let := quiver A
  let := spanningTreeArborescence A
  let := groupoid_isThin A
  intro X Y
  exact RootedFinite.colimit_isWeaklyContractible (spanningTree A) X Y

lemma hammockValueFiber_isWeaklyContractible (Y : Paths Q)
    (β : (Quiver.FreeGroupoid.of Q).obj A ⟶ positiveEvaluation.obj Y) :
    IsWeaklyContractible (hammockValueFiber A Y β) := by
  let := quiver A
  let e := hammockValueFiberCoverIso A Y β
  have ht : terminal.from _ = e.hom ≫ terminal.from _ := terminal.hom_ext _ _
  change IsWeakHomotopyEquivalence (terminal.from (hammockValueFiber A Y β))
  rw [ht]
  exact (isPrecompositionEquivalence_of_iso e).isWeakHomotopyEquivalence.comp
    (colimit_isWeaklyContractible A _ _)

lemma existingHammockValueFiber_isWeaklyContractible {Q' : Type u} [Quiver.{u} Q']
    (A' : Q') (Y' : Paths Q')
    (β' : (Quiver.FreeGroupoid.of Q').obj A' ⟶ positiveEvaluation.obj Y') :
    IsWeaklyContractible (SimplicialValueFiber.space
      (Zigzag.Value.colimitValue positiveEvaluation positiveEvaluation_inverts_top
        ((Paths.of Q').obj A') Y') β') := by
  let := quiver A'
  let e := existingHammockValueFiberCoverIso A' Y' β'
  have ht : terminal.from _ = e.hom ≫ terminal.from _ := terminal.hom_ext _ _
  change IsWeakHomotopyEquivalence (terminal.from _)
  rw [ht]
  exact (isPrecompositionEquivalence_of_iso e).isWeakHomotopyEquivalence.comp
    (colimit_isWeaklyContractible A' _ _)

end SerrePositivity.EInfinity.Hammock.FreeQuiverCover
