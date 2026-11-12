module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.CoherentFilteredLimitExchange
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.EmptyShapeConeCriterion
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.CoherentFilteredTerminal

/-!
概要：一般 coherent filtered 図式の極限交換の空形状の場合を証明する。
方針：元の全錐の族を頂点で評価し、各値の終対象性を元の余極限余錐へ移す。
規約：元の余錐・錐全体を保持。使われ方：有限形状のセル帰納の空形状の条件。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 空形状について、元の coherent な錐の族の点ごとの filtered 余極限は極限錐。 -/
lemma coherentFilteredLimitExchangeShape_of_empty (K : SSet.{u}) (hK : ¬ K.Nonempty) :
    CoherentFilteredLimitExchangeShape K := by
  intro B hB hfil p c hc hinner
  let L := (SSet.uliftFunctor.{u + 1, u}).obj K
  have hL : ¬ L.Nonempty := by
    rintro ⟨x⟩
    exact hK ⟨x.down⟩
  let k := (joinInl (Δ[0] : SSet.{u + 1}) L).app (Opposite.op ⦋0⦌)
    (SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u + 1})))
  have hp : ∀ b : B _⦋0⦌,
      IsTerminalVertex ((p ≫ evaluateFunctorAt k).app (Opposite.op ⦋0⦌) (ULift.up b)) := by
    intro b
    have ht := (isLimitCone_emptyShape_iff_vertex hL
      (functorVertexCone (p.app (Opposite.op ⦋0⦌) (ULift.up b)))).mp (hinner b)
    rw [functorVertexCone_vertex] at ht
    exact ht
  have hout := coherentFilteredColimitVertex_isTerminal (p ≫ evaluateFunctorAt k) hp
    (evaluateFunctorCocone c k) (hc k)
  apply (isLimitCone_emptyShape_iff_vertex hL (functorVertexCone c.vertex)).mpr
  rw [functorVertexCone_vertex]
  rw [evaluateFunctorCocone_vertex] at hout
  exact hout

/-- 有限セル帰納に現れる元の空部分複体の形状でも交換が成り立つ。 -/
lemma coherentFilteredLimitExchangeShape_empty (X : SSet.{u}) :
    CoherentFilteredLimitExchangeShape (⊥ : X.Subcomplex) := by
  apply coherentFilteredLimitExchangeShape_of_empty
  rintro ⟨x⟩
  exact x.property

end SerrePositivity.InfinityCategories.F2
