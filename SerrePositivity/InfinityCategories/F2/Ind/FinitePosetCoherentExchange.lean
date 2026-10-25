module

public import SerrePositivity.InfinityCategories.F2.Ind.FiniteWithInitialFilteredLimits
public import SerrePositivity.InfinityCategories.F2.Presentable.CoherentFilteredPosetExchange
public import SerrePositivity.InfinityCategories.F2.Ind.FiniteLimitExchangeInput

/-!
概要：有限 poset の極限と一般 coherent filtered 余極限の交換を証明する。
方針：元の全錐族を cofinal poset に制限し、共同 strict 化した有限交換から戻す。
規約：指定余錐の頂点と全脚を保持し、濃度変更境界を入力しない。
使われ方：I-2 d′ の cospan 交換と全有限形状への帰納。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
open Presentable HomotopyLimits

/-- 通常 filtered 添字の元の全錐族は、有限 poset 上の極限性を保つ。 -/
lemma coherentFilteredLimitExchange_nerve_finite_poset
    (I : Type u) [PartialOrder I] [Finite I]
    (J : Type u) [SmallCategory J] [IsFiltered J]
    (F : (SSet.uliftFunctor.{u + 1, u}).obj (nerve J) ⟶
      (ihom (join (Δ[0] : SSet.{u + 1})
        ((SSet.uliftFunctor.{u + 1, u}).obj (nerve I)))).obj SpaceInfinity.{u})
    (c : JoinCocone F) (hc : IsPointwiseColimitCone c)
    (hF : ∀ j, IsLimitCone (functorVertexCone (F.app
      (Opposite.op ⦋0⦌) (ULift.up (nerveVertex j))))) :
    IsLimitCone (functorVertexCone c.vertex) := by
  apply (coneFamilyModelStrictLimit_iff F c hc).mp
  apply finiteWithInitialFilteredColimit_isLimit I J
  intro j
  exact (coneFamilyStage_isLimit_iff F j).mpr (hF j)

/-- 一般 filtered ∞ 添字についても、有限 poset 形状の元の全錐交換が成立する。 -/
lemma coherentFilteredLimitExchangeShape_finite_poset
    (I : Type u) [PartialOrder I] [Finite I] :
    CoherentFilteredLimitExchangeShape (nerve I) := by
  intro B hB hFiltered F c hc hF
  let : Fact (Cardinal.aleph0.{u}).IsRegular := ⟨Cardinal.isRegular_aleph0⟩
  have : IsKappaFiltered Cardinal.aleph0.{u} B :=
    (isKappaFiltered_aleph0_iff B).mpr hFiltered
  obtain ⟨J, o, f, hJ, _, hf⟩ := exists_cofinal_kappaFiltered_poset
    (κ := Cardinal.aleph0.{u}) B
  let := o
  have := hJ
  have : IsFiltered J := (isCardinalFiltered_aleph0_iff J).mp hJ
  let r := (SSet.uliftFunctor.{u + 1, u}).map f
  have ht := coherentFilteredLimitExchange_nerve_finite_poset I J
    (r ≫ F) (c.restrict r)
    (pointwiseColimitCocone_restrict_rightCofinal c hc r (isRightCofinal_ulift f hf))
    (fun j ↦ hF (f.app (Opposite.op ⦋0⦌) (nerveVertex j)))
  rwa [JoinCocone.vertex_restrict] at ht

end SerrePositivity.InfinityCategories.F2.Ind
