module

public import SerrePositivity.InfinityCategories.F2.Ind.ChosenColimitFamilyLimits
public import SerrePositivity.InfinityCategories.Core.FunctorPointwiseLimitExistence
public import SerrePositivity.InfinityCategories.F2.Presentable.PointwiseColimitPrecomposition

/-!
概要：全錐族の交換と、同じ選択した余極限関手の極限保存を相互に移す。
方針：変数交換した指定全錐と選択余錐を比較し、元の指定余極限へ一意性で戻す。
規約：元の完成頂点と全錐を保持する。形状や添字の有限性はここでは不要。
使われ方：I-2 d′ の全有限形状への帰納。
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

/-- 固定した添字と標的についての、元の全錐族の点ごとの余極限による極限性保存。 -/
def ConeFamilyLimitExchange (B K X : SSet.{u}) : Prop :=
  ∀ (F : B ⟶ (ihom (join (Δ[0] : SSet.{u}) K)).obj X) (c : JoinCocone F),
    IsPointwiseColimitCone c →
    (∀ b, IsLimitCone (functorVertexCone (F.app (Opposite.op ⦋0⦌) b))) →
    IsLimitCone (functorVertexCone c.vertex)

/-- 元の全錐交換から、同じ選択した余極限関手による任意の極限錐の保存。 -/
lemma chosenColimit_map_isLimit_of_exchange {B K X : SSet.{u}} [Quasicategory X]
    (hX : ∀ p : B ⟶ X, HasColimit p) (hK : ∀ p : K ⟶ X, HasLimit p)
    (hex : ConeFamilyLimitExchange B K X) {p : K ⟶ (ihom B).obj X}
    (c : JoinCone p) (hc : IsLimitCone c) :
    IsLimitCone (mapJoinCone (chosenColimitFunctor B X hX) c) := by
  have hp : HasPointwiseLimits p := fun b ↦ hK _
  have hcp := isPointwiseLimitCone_of_isLimitCone_of_hasPointwiseLimits hp c hc
  apply (chosenColimitParameterCompletedLimit_iff hX c).mp
  apply hex _ (chosenColimitParameterCocone hX c.val)
    (chosenColimitParameterCocone_pointwise hX c.val)
  intro b
  exact (functorVertexCone_flip_isLimit_iff c b).mpr (hcp b)

/-- 同じ余極限関手による極限保存から、元の任意の指定点ごとの全余錐の交換へ戻す。 -/
lemma coneFamilyLimitExchange_of_chosenColimit_preservesLimits
    {B K X : SSet.{u}} [Quasicategory X]
    (hX : ∀ p : B ⟶ X, HasColimit p)
    (hU : ∀ (p : K ⟶ (ihom B).obj X) (c : JoinCone p), IsLimitCone c →
      IsLimitCone (mapJoinCone (chosenColimitFunctor B X hX) c)) :
    ConeFamilyLimitExchange B K X := by
  intro F c hc hF
  let q : JoinCone (joinInr (Δ[0] : SSet.{u}) K ≫
      internalHomFlipHomEquiv _ _ _ F) := ⟨internalHomFlipHomEquiv _ _ _ F, rfl⟩
  have hq : internalHomFlipHomEquiv _ _ _ q.val = F :=
    (internalHomFlipHomEquiv B (join (Δ[0] : SSet.{u}) K) X).left_inv F
  have hqp : IsPointwiseLimitCone q := by
    intro b
    apply (functorVertexCone_flip_isLimit_iff q b).mp
    rw [hq]
    exact hF b
  let d := chosenColimitParameterCocone hX q.val
  have hd := chosenColimitParameterCocone_pointwise hX q.val
  have ht := (chosenColimitParameterCompletedLimit_iff hX q).mpr
    (hU _ q (isLimitCone_of_pointwise q hqp))
  let e := coherentCoconeOfDiagramEq hq d
  have he := pointwiseColimitCocone_diagramEq hq d hd
  have hv : e.vertex = d.vertex := congrArg
    (fun f ↦ SSet.yonedaEquiv (joinInr B (Δ[0] : SSet.{u}) ≫ f))
    (coherentCoconeOfDiagramEq_val hq d)
  apply (pointwiseColimitCompletedLimit_iff e c he hc).mp
  rw [hv]
  exact ht

end SerrePositivity.InfinityCategories.F2.Ind
