module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.CoherentFilteredLimitExchange
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FunctorCoconeReindex
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FunctorVertexConeReindex

/-!
概要：一般 coherent filtered 極限交換は元の形状の厳密な同型で不変。
方針：元の全余錐を同型形状で前合成し、点ごとの余極限性と錐の極限性を移す。
規約：元の余錐・錐の全単体を保持。使われ方：有限セル帰納の同型不変性の条件。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の形状の同型は、coherent filtered 極限交換の性質を移す。 -/
lemma coherentFilteredLimitExchangeShape_of_iso {K L : SSet.{u}} (e : K ≅ L)
    (hK : CoherentFilteredLimitExchangeShape K) : CoherentFilteredLimitExchangeShape L := by
  intro B hB hfil p c hc hinner
  let f := (SSet.uliftFunctor.{u + 1, u}).map e.hom
  have : IsIso f := by dsimp only [f]; infer_instance
  let j := joinMap (𝟙 (Δ[0] : SSet.{u + 1})) f
  let d := reindexFunctorCocone c j
  have hd : IsPointwiseColimitCone d := hc.reindex j
  have hi : ∀ b : B _⦋0⦌, IsLimitCone (functorVertexCone
      ((p ≫ (pre j).app SpaceInfinity.{u}).app (Opposite.op ⦋0⦌) (ULift.up b))) := by
    intro b
    exact (isLimitCone_functorVertexCone_reindex_iff f
      (p.app (Opposite.op ⦋0⦌) (ULift.up b))).mpr (hinner b)
  have hz := hK B (p ≫ (pre j).app SpaceInfinity.{u}) d hd hi
  rw [reindexFunctorCocone_vertex] at hz
  exact (isLimitCone_functorVertexCone_reindex_iff f c.vertex).mp hz

/-- 同型な二形状では、元の coherent filtered 極限交換は同値な条件。 -/
lemma coherentFilteredLimitExchangeShape_iff_of_iso {K L : SSet.{u}} (e : K ≅ L) :
    CoherentFilteredLimitExchangeShape K ↔ CoherentFilteredLimitExchangeShape L :=
  ⟨coherentFilteredLimitExchangeShape_of_iso e,
    coherentFilteredLimitExchangeShape_of_iso e.symm⟩

end SerrePositivity.InfinityCategories.F2
