module

public import SerrePositivity.InfinityCategories.F2.Presentable.CardinalExchangeReflection
public import SerrePositivity.InfinityCategories.F2.Presentable.AccessibleFunctor

/-!
概要：全極限錐族の各脚の filtered 余極限保存から頂点の同じ保存性を導く。
方針：元の全余錐を錐族へ送り、形状交換と全錐の各点反映を適用する。
規約：全族を入力にし、各点だけの比較から自然性を仮定しない。
使われ方：引き戻し内の共変 Hom の compact 性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 概要：各脚が μ-filtered 余極限を保つ全極限錐族では頂点も同じ余極限を保つ。
方針：元の全余錐について、各脚の余極限性を形状交換で頂点へ反映する。
規約：形状交換は明示し、元の関手・図式・指定余錐を保持する。
使われ方：cospan の共変 Hom 全族から引き戻し候補の compact 性を導く。 -/
lemma isKappaAccessibleFunctor_limitFamily_apex
    {μ : Cardinal.{u}} {K : SSet.{u}} {X : SSet.{u + 1}}
    (F : X ⟶ (ihom (join (Δ[0] : SSet.{u + 1})
      ((SSet.uliftFunctor.{u + 1, u}).obj K))).obj SpaceInfinity.{u})
    (hF : ∀ x : X _⦋0⦌, IsLimitCone (functorVertexCone (F.app (Opposite.op ⦋0⦌) x)))
    (hK : CardinalFilteredLimitExchangeShape μ K)
    (hleg : ∀ k : ((SSet.uliftFunctor.{u + 1, u}).obj K) _⦋0⦌,
      IsKappaAccessibleFunctor μ (F ≫ evaluateFunctorAt
        ((joinInr (Δ[0] : SSet.{u + 1}) _).app (Opposite.op ⦋0⦌) k))) :
    IsKappaAccessibleFunctor μ (F ≫ evaluateFunctorAt
      (yonedaEquiv (joinInl (Δ[0] : SSet.{u + 1}) _))) := by
  intro J hJ hμ D c hc
  let R := coneRestriction ((SSet.uliftFunctor.{u + 1, u}).obj K) SpaceInfinity.{u}
  have hr : IsPointwiseColimitCone (mapJoinCocone R (mapJoinCocone F c)) := by
    intro k
    have h := hleg k J D c hc
    apply (isColimitCone_iff_of_cocone_val_eq
      (evaluateFunctorCocone (mapJoinCocone R (mapJoinCocone F c)) k)
      (mapJoinCocone (F ≫ evaluateFunctorAt
        ((joinInr (Δ[0] : SSet.{u + 1}) _).app (Opposite.op ⦋0⦌) k)) c) ?_).mpr h
    change ((c.val ≫ F) ≫ R) ≫ evaluateFunctorAt k = c.val ≫ (F ≫ evaluateFunctorAt _)
    simp only [R, coneRestriction, Category.assoc, evaluateFunctorAt_pre]
  have hfull := pointwiseColimit_of_cardinalExchange hK (D ≫ F)
    (fun j ↦ hF (D.app _ (ULift.up j))) (mapJoinCocone F c)
    (by rw [Ind.mapJoinCocone_vertex]; exact hF c.vertex) hr
  apply (isColimitCone_iff_of_cocone_val_eq
    (mapJoinCocone (F ≫ evaluateFunctorAt
      (yonedaEquiv (joinInl (Δ[0] : SSet.{u + 1}) _))) c)
    (evaluateFunctorCocone (mapJoinCocone F c)
      (yonedaEquiv (joinInl (Δ[0] : SSet.{u + 1}) _))) (Category.assoc _ _ _).symm).mpr
  exact hfull _

end SerrePositivity.InfinityCategories.F2.Presentable
