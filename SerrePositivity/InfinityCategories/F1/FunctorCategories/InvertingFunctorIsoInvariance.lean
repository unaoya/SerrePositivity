module

public import SerrePositivity.InfinityCategories.F1.Transport.SimplexRestrictionInner

/-!
概要：指定辺を反転する関手の条件の、coherent な関手同型に関する不変性。
方針：ホモトピー圏に誘導される自然同型で、各辺の像の可逆性を比較する。
規約：始域と標的の quasicategory 性は不要。
使われ方：可逆な比較の延長を、反転関手の全部分複体へ戻す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- coherent に同型な関手が反転する辺の集合は等しい。 -/
lemma invertedEdges_functorIso {X E : SSet.{u}} {F G : X ⟶ E} (e : FunctorIso F G) :
    invertedEdges F = invertedEdges G := by
  apply Set.ext
  intro s
  exact NatIso.isIso_map_iff e.toNatIso
    (SSet.Truncated.HomotopyCategory.homMk (edgeOfSimplex s))

/-- 指定された全ての辺の反転条件は、関手同型で保たれ反映される。 -/
lemma FunctorIso.invertsEdges_iff {X E : SSet.{u}} {F G : X ⟶ E}
    (e : FunctorIso F G) (W : Set (X _⦋1⦌)) : InvertsEdges F W ↔ InvertsEdges G W := by
  unfold InvertsEdges
  rw [invertedEdges_functorIso e]

/-- 反転関手の全部分複体の頂点条件は、周囲の関手圏の同型で不変。 -/
lemma isInvertingFunctorVertex_iff_of_vertexIso {X E : SSet.{u}}
    (W : Set (X _⦋1⦌)) {v w : ((ihom X).obj E) _⦋0⦌} (e : VertexIso v w) :
    IsInvertingFunctorVertex X E W v ↔ IsInvertingFunctorVertex X E W w := by
  obtain ⟨F, rfl⟩ := (functorVertexEquiv X E).surjective v
  obtain ⟨G, rfl⟩ := (functorVertexEquiv X E).surjective w
  unfold IsInvertingFunctorVertex
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  exact FunctorIso.invertsEdges_iff e W

end SerrePositivity.InfinityCategories
