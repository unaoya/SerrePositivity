module

public import SerrePositivity.InfinityCategories.F2.Ind.ArrowInterpolationCorner
public import SerrePositivity.InfinityCategories.F2.Ind.IndCommaKappaCocone
public import SerrePositivity.InfinityCategories.F1.UniversePushouts

/-!
概要：元の円柱族と新しい始点余錐を同じ実 Ind comma 内で同時に上から抑える。
方針：宇宙持ち上げ後の同じ pushout に全図式を貼り、局所 κ-small 余錐を取る。
規約：二つの元の全図式と共通境界を厳密に保つ。使われ方：射の二段表示の終点追加。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 同じ元の円柱族と始点余錐は、貼り合わせた実 comma 図式の一つの余錐を持つ。 -/
lemma exists_indComma_arrowInterpolation_cocone (κ : Cardinal.{u}) [Fact κ.IsRegular]
    {C A : SSet.{u}} [Quasicategory C] (x : (IndInfinity κ C) _⦋0⦌)
    (hA : IsKappaSmall κ A)
    (F : (SSet.uliftFunctor.{u + 1, u}).obj (A ⊗ Δ[1]) ⟶
      leftKanShape (indYoneda κ C) x)
    (G : (SSet.uliftFunctor.{u + 1, u}).obj (join A (Δ[0] : SSet.{u})) ⟶
      leftKanShape (indYoneda κ C) x)
    (h : (SSet.uliftFunctor.{u + 1, u}).map SSet.ι₀ ≫ F =
      (SSet.uliftFunctor.{u + 1, u}).map (joinInl A Δ[0]) ≫ G) :
    ∃ H : (SSet.uliftFunctor.{u + 1, u}).obj (arrowInterpolationCorner A) ⟶
        leftKanShape (indYoneda κ C) x,
      Nonempty (JoinCocone H) ∧
      (SSet.uliftFunctor.{u + 1, u}).map
        (pushout.inl SSet.ι₀ (joinInl A (Δ[0] : SSet.{u}))) ≫ H = F ∧
      (SSet.uliftFunctor.{u + 1, u}).map
        (pushout.inr SSet.ι₀ (joinInl A (Δ[0] : SSet.{u}))) ≫ H = G := by
  let hp := uliftSSet_isPushout.{u, u + 1}
    (IsPushout.of_hasPushout (SSet.ι₀ : A ⟶ A ⊗ Δ[1]) (joinInl A Δ[0]))
  let H := hp.desc F G h
  have hc := nonempty_indComma_cocone κ x
    (arrowInterpolationCorner_isKappaSmall (Fact.out : κ.IsRegular) hA) H
  exact ⟨H, hc, hp.inl_desc F G h, hp.inr_desc F G h⟩

end SerrePositivity.InfinityCategories.F2.Ind
