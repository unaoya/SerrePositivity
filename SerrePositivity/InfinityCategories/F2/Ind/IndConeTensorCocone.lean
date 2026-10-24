module

public import SerrePositivity.InfinityCategories.F2.Ind.ConeTensorCorner
public import SerrePositivity.InfinityCategories.F2.Ind.IndCommaKappaCocone
public import SerrePositivity.InfinityCategories.F1.Universe.Pushouts

/-!
概要：元の試験族と下方余錐を、同じ実 Ind comma 内の一つの余錐で上から抑える。
方針：元の pushout を宇宙移送し、κ-small な補間領域の実余錐を取る。
規約：一般の κ-small な両形状と指定された全境界を保持する。
使われ方：有限半順序形状の点追加における相対補間。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
/-- 概要：元の二つの境界を保つ補間領域上の実余錐が存在する。
方針：全図式を貼り局所余錐を取る。規約：元の全射。使われ方：元の積への拡張。 -/
lemma exists_indComma_coneTensor_cocone (κ : Cardinal.{u}) [Fact κ.IsRegular]
    {C A L : SSet.{u}} [Quasicategory C] (x : (IndInfinity κ C) _⦋0⦌)
    (hA : IsKappaSmall κ A) (hL : IsKappaSmall κ L)
    (F : (SSet.uliftFunctor.{u + 1, u}).obj (A ⊗ join L (Δ[0] : SSet.{u})) ⟶
      leftKanShape (indYoneda κ C) x)
    (G : (SSet.uliftFunctor.{u + 1, u}).obj (join A (Δ[0] : SSet.{u}) ⊗ L) ⟶
      leftKanShape (indYoneda κ C) x)
    (h : (SSet.uliftFunctor.{u + 1, u}).map (A ◁ joinInl L (Δ[0] : SSet.{u})) ≫ F =
      (SSet.uliftFunctor.{u + 1, u}).map (joinInl A (Δ[0] : SSet.{u}) ▷ L) ≫ G) :
    ∃ H : (SSet.uliftFunctor.{u + 1, u}).obj (coneTensorCorner A L) ⟶
        leftKanShape (indYoneda κ C) x,
      Nonempty (JoinCocone H) ∧
      (SSet.uliftFunctor.{u + 1, u}).map
        (pushout.inl (A ◁ joinInl L (Δ[0] : SSet.{u})) (joinInl A Δ[0] ▷ L)) ≫ H = F ∧
      (SSet.uliftFunctor.{u + 1, u}).map
        (pushout.inr (A ◁ joinInl L (Δ[0] : SSet.{u})) (joinInl A Δ[0] ▷ L)) ≫ H = G := by
  let hp := uliftSSet_isPushout.{u, u + 1}
    (IsPushout.of_hasPushout (A ◁ joinInl L (Δ[0] : SSet.{u})) (joinInl A Δ[0] ▷ L))
  let H := hp.desc F G h
  have hc := nonempty_indComma_cocone κ x
    (coneTensorCorner_isKappaSmall (Fact.out : κ.IsRegular) hA hL) H
  exact ⟨H, hc, hp.inl_desc F G h, hp.inr_desc F G h⟩

end SerrePositivity.InfinityCategories.F2.Ind
