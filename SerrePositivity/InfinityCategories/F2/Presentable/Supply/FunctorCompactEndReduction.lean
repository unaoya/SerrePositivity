module

public import SerrePositivity.InfinityCategories.F2.Presentable.Supply.FunctorEndCoefficient
public import SerrePositivity.InfinityCategories.F2.Presentable.Supply.TwistedArrowLimitContinuity

/-!
概要：P-12 の最終 compact 判定を、元の全 Hom を頂点とする end 極限錐族へ還元する。
方針：end 係数の評価脚の保存と κ-small twisted arrow の極限の保存を合成する。
規約：極限錐族の存在はこの葉では結論せず、元の全自然な族を明示的に受け取る。
使われ方：全 Hom の end 比較の構成後に適用する最終接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 概要：指定された全 Hom の end 極限錐族から、点ごとに compact な関手の compact 性。
方針：係数の各脚の保存を twisted arrow 極限錐族の頂点へ反映する。
規約：極限性・係数との一致・元の Hom との一致を全自然な族として要求する。
使われ方：P-12 の end 比較を最終命題へ接続する。 -/
lemma isKappaCompact_functorVertex_of_endFamily
    {κ : Cardinal.{u}} [Fact κ.IsRegular] (hκ : Cardinal.aleph0 < κ)
    {K : SSet.{u}} [Quasicategory K] (hK : IsKappaSmall κ K)
    {C : SSet.{u + 1}} [Quasicategory C] (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits C)
    (F : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ C)
    (hF : ∀ k, Compact.IsKappaCompact.{u, u + 1} κ (F.app _ k))
    (E : (SSet.uliftFunctor.{u + 2, u + 1}).obj
        ((ihom ((SSet.uliftFunctor.{u + 1, u}).obj K)).obj C) ⟶
      (ihom (join (Δ[0] : SSet.{u + 2})
        ((SSet.uliftFunctor.{u + 2, u + 1}).obj
          (TwistedArrow ((SSet.uliftFunctor.{u + 1, u}).obj K))))).obj SpaceInfinity.{u + 1})
    (hE : ∀ g, IsLimitCone (functorVertexCone (E.app (Opposite.op ⦋0⦌) g)))
    (hr : FunctorIso (E ≫ coneRestriction
        ((SSet.uliftFunctor.{u + 2, u + 1}).obj
          (TwistedArrow ((SSet.uliftFunctor.{u + 1, u}).obj K))) SpaceInfinity.{u + 1})
      (functorEndCoefficient F))
    (ha : FunctorIso (E ≫ evaluateFunctorAt (yonedaEquiv (joinInl (Δ[0] : SSet.{u + 2})
        ((SSet.uliftFunctor.{u + 2, u + 1}).obj
          (TwistedArrow ((SSet.uliftFunctor.{u + 1, u}).obj K))))))
      (covariantRepresentableInfinity (functorVertex F))) :
    Compact.IsKappaCompact.{u, u + 1} κ (functorVertex F) := by
  have hleg (t : ((SSet.uliftFunctor.{u + 2, u + 1}).obj
      (TwistedArrow ((SSet.uliftFunctor.{u + 1, u}).obj K))) _⦋0⦌) :
      Compact.PreservesKappaFilteredColimits.{u, u + 1} κ
        (E ≫ evaluateFunctorAt
          ((joinInr (Δ[0] : SSet.{u + 2}) _).app (Opposite.op ⦋0⦌) t)) := by
    have ht : E ≫ evaluateFunctorAt
        ((joinInr (Δ[0] : SSet.{u + 2}) _).app (Opposite.op ⦋0⦌) t) =
        (E ≫ coneRestriction _ SpaceInfinity.{u + 1}) ≫ evaluateFunctorAt t := by
      simp only [coneRestriction, Category.assoc, evaluateFunctorAt_pre]
    rw [ht]
    obtain ⟨t⟩ := t
    exact (functorEndCoefficient_evaluation_preservesKappaFilteredColimits hC F hF t).of_functorIso
      (hr.postcomp (evaluateFunctorAt (ULift.up t))).symm
  have h := preservesKappaFilteredColimits_twistedArrowLimitFamily_apex.{u, u + 1}
    hκ K hK E hE hleg
  exact h.of_functorIso ha

end SerrePositivity.InfinityCategories.F2.Presentable
