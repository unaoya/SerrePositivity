module

public import SerrePositivity.InfinityCategories.F2.Presentable.WithInitialFilteredLimits
public import SerrePositivity.InfinityCategories.F2.Presentable.ConeFamilyModelColimit

/-!
概要：小さい poset の極限と μ-filtered な coherent 錐族の指定点ごとの余極限の交換。
方針：全錐族を共同 strict 化し、元の strict 余極限の極限性を証明して、指定余錐へ戻す。
規約：元の全図式・全錐・指定余極限を保持する。交換定理を仮定や instance に入れない。
使われ方：μ-small κ-filtered 部分表示の μ-compact 性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable
open HomotopyLimits

/-- 元の coherent 全錐族の各段階が極限なら、同じ指定点ごとの μ-filtered 余極限の全錐も極限。 -/
lemma coherentCardinalFilteredLimitExchange_nerve_poset
    {κ μ : Cardinal.{u}} [Fact κ.IsRegular] [Fact μ.IsRegular]
    (h : IsCardinalChangeBound κ μ) (I : Type u) [PartialOrder I] (hI : HasCardinalLT I μ)
    (J : Type u) [SmallCategory J] [IsCardinalFiltered J μ]
    (F : (SSet.uliftFunctor.{u + 1, u}).obj (nerve J) ⟶
      (ihom (join (Δ[0] : SSet.{u + 1})
        ((SSet.uliftFunctor.{u + 1, u}).obj (nerve I)))).obj SpaceInfinity.{u})
    (c : JoinCocone F) (hc : IsPointwiseColimitCone c)
    (hF : ∀ j, IsLimitCone (functorVertexCone (F.app
      (Opposite.op ⦋0⦌) (ULift.up (nerveVertex j))))) :
    IsLimitCone (functorVertexCone c.vertex) := by
  have := isFiltered_of_isCardinalFiltered J μ
  apply (coneFamilyModelStrictLimit_iff F c hc).mp
  apply withInitialFilteredColimit_isLimit h I hI J
  intro j
  exact (coneFamilyStage_isLimit_iff F j).mpr (hF j)

end SerrePositivity.InfinityCategories.F2.Presentable
