module

public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafAllSmallLimits
public import SerrePositivity.InfinityCategories.F2.Ind.FunctorFilteredColimits
public import SerrePositivity.InfinityCategories.F2.Ind.FullConeLift
public import SerrePositivity.InfinityCategories.F2.Ind.FiniteLimitExchangeInput
public import SerrePositivity.InfinityCategories.Core.FilteredExchange.FunctorCoconePostcompose

/-!
概要：Ind 内の全極限錐族の filtered 補完は、明示交換入力のもとで再び極限錐となる。
方針：同じ全余錐を前層の各点で評価し、空間値交換と全部分包含の反映へ渡す。
規約：元の全族とその点ごとの余極限余錐を固定する。交換定理の証拠は仮定のまま。
使われ方：有限図式の単一 filtered 表示から極限全錐を構成する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 同じ全錐族の点ごとの filtered 補完は、前層の全評価での交換から極限錐となる。 -/
lemma ind_filteredLimitCone_isLimit (κ : Cardinal.{u}) (hκ : Cardinal.aleph0 ≤ κ)
    {I K C : SSet.{u}} [Quasicategory I] [IsKappaFiltered κ I] [Quasicategory C]
    (hex : CoherentFilteredLimitExchangeShape K)
    (p : (SSet.uliftFunctor.{u + 1, u}).obj I ⟶
      (ihom (join (Δ[0] : SSet.{u + 1}) ((SSet.uliftFunctor.{u + 1, u}).obj K))).obj
        (IndInfinity κ C))
    (c : JoinCocone p)
    (hc : ∀ k, IsColimitCone (mapJoinCocone (indInclusionPresheaf κ C)
      (evaluateFunctorCocone c k)))
    (hp : ∀ i : I _⦋0⦌, IsLimitCone (mapJoinCone (indInclusionPresheaf κ C)
      (functorVertexCone (p.app (Opposite.op ⦋0⦌) (ULift.up i))))) :
    IsLimitCone (functorVertexCone c.vertex) ∧
      IsLimitCone (mapJoinCone (indInclusionPresheaf κ C) (functorVertexCone c.vertex)) := by
  let F := indInclusionPresheaf κ C
  have hlim : IsLimitCone (mapJoinCone F (functorVertexCone c.vertex)) := by
    apply presheafInfinity_isLimit_of_evaluation
    intro x
    let G := F ≫ presheafInfinityEvaluation x
    let H := (ihom (join (Δ[0] : SSet.{u + 1})
      ((SSet.uliftFunctor.{u + 1, u}).obj K))).map G
    let : IsFilteredInfinity I := isFilteredInfinity_of_isKappaFiltered hκ I
    have he : IsPointwiseColimitCone (mapJoinCocone H c) := by
      apply IsPointwiseColimitCone.postcompose c G
      intro k
      exact presheafInfinity_evaluation_isColimit _ _ (hc k) x
    have hr (i : I _⦋0⦌) : IsLimitCone (functorVertexCone
        ((p ≫ H).app (Opposite.op ⦋0⦌) (ULift.up i))) := by
      apply (functorVertexCone_postcompose_isLimit_iff _ G).mpr
      exact presheafInfinity_evaluation_small_isLimit _ _ (hp i) x
    have ht := hex I (p ≫ H) (mapJoinCocone H c) he hr
    exact (functorVertexCone_postcompose_isLimit_iff c.vertex G).mp ht
  exact ⟨ind_isLimit_of_inclusion κ _ _ hlim, hlim⟩

end SerrePositivity.InfinityCategories.F2.Ind
