module

public import SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback.SeededAlternatingFactorization

/-!
概要：入力付き相対余錐から次の閉前置段を実際に構成する。
方針：全余錐と成分余錐の形状比較を使い、同じ入力の coslice 内で延長する。
規約：元の入力図式と両表示添字を保持する。
使われ方：入力付き相対交互塔の実際の再帰段。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback

variable {κ : Cardinal.{u}} {K : SSet.{u}} {B : SSet.{u + 1}}
  {x : (Δ[0] : SSet.{u + 1}) ⟶ B} {I : Fin 2 → SSet.{u}}
  {P : ∀ c, (SSet.uliftFunctor.{u + 1, u}).obj (I c) ⟶ sliceOver x}
  {z : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ sliceOver x}

/-- 概要：入力付き閉前置段が元の入力付き厳密前置段を保持する条件。
方針：元の段の保持条件と coslice 内の全前置制限を記録する。
規約：入力図式の全単体を保持する。
使われ方：次の段から全過去段への整合。 -/
def SeededAlternatingClosedStage.ExtendsOpen {a : AlternatingIndex κ}
    (r : SeededAlternatingClosedStage (κ := κ) (I := I) (P := P) z a)
    (s : SeededAlternatingOpenStage (κ := κ) (I := I) (P := P) z a) : Prop :=
  r.stage.ExtendsOpen s.stage ∧
    (SSet.uliftFunctor.{u + 1, u}).map (nerveMap (strictPrefixToClosed a)) ≫ r.under = s.under

/-- 概要：具体的な入力付き成分余錐から次の入力付き閉前置段が存在する。
方針：同じ全余錐を閉前置形状へ移し、現在成分だけ元の表示添字を延長する。
規約：元の入力と全過去の表示添字を保持する。
使われ方：相対因子化存在定理から実際の段延長を得る。 -/
lemma exists_seededClosedStage_of_cocone (a : κ.ord.ToType) (c : Fin 2)
    {s : SeededAlternatingOpenStage (κ := κ) (I := I) (P := P) z (toLex (a, c))}
    (j : JoinCocone (s.stage.index c)) (d : JoinCocone s.under)
    (hc : joinMap ((SSet.uliftFunctor.{u + 1, u}).map
        (nerveMap (alternatingLowerSection κ (toLex (a, c)) c))) (𝟙 Δ[0]) ≫
        d.val ≫ sliceUnderProjection z =
      (((uliftSliceUnderIso.{u, u + 1} (s.stage.index c)).hom.app (Opposite.op ⦋0⦌))
        (ULift.up j)).val ≫ P c) :
    ∃ r : SeededAlternatingClosedStage (κ := κ) (I := I) (P := P) z (toLex (a, c)),
      r.ExtendsOpen s := by
  classical
  let e := liftedCoconeIso.{u, u + 1} (F1B.posetLowerJoinIso (toLex (a, c)))
  let U := e.inv ≫ d.val
  have hold : (SSet.uliftFunctor.{u + 1, u}).map
      (nerveMap (strictPrefixToClosed (toLex (a, c)))) ≫ U = s.under := by
    have h : (SSet.uliftFunctor.{u + 1, u}).map
        (nerveMap (strictPrefixToClosed (toLex (a, c)))) = joinInl _ Δ[0] ≫ e.hom := by
      simp only [e, liftedCoconeIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
      rw [← Category.assoc, uliftCoconeShapeIso_inv_inl, ← CategoryTheory.Functor.map_comp,
        F1B.posetLowerJoinIso_inl]
      rfl
    dsimp only [U]
    rw [h, Category.assoc, Iso.hom_inv_id_assoc]
    exact d.property
  have hcur : (SSet.uliftFunctor.{u + 1, u}).map
      (nerveMap (alternatingClosedSection κ (toLex (a, c)) c)) ≫ (U ≫ sliceUnderProjection z) =
      (SSet.uliftFunctor.{u + 1, u}).map (extendedComponentIndex κ a c j) ≫ P c := by
    apply (cancel_epi (liftedCoconeIso.{u, u + 1} (componentConeIso κ a c)).hom).1
    have h := liftedCoconeIso_naturality.{u, u + 1}
      (componentConeIso κ a c) (F1B.posetLowerJoinIso (toLex (a, c)))
      (nerveMap (alternatingLowerSection κ (toLex (a, c)) c))
      (nerveMap (alternatingClosedSection κ (toLex (a, c)) c))
      (alternatingConeShape_component κ a c)
    rw [← Category.assoc, ← h]
    change (_ ≫ e.hom) ≫ (e.inv ≫ d.val ≫ sliceUnderProjection z) = _
    rw [Category.assoc, Iso.hom_inv_id_assoc, hc]
    simp only [liftedCoconeIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
      extendedComponentIndex, CategoryTheory.Functor.map_comp, Category.assoc]
    rw [← Category.assoc ((SSet.uliftFunctor.{u + 1, u}).map (componentConeIso κ a c).hom),
      ← CategoryTheory.Functor.map_comp, Iso.hom_inv_id,
      (SSet.uliftFunctor.{u + 1, u}).map_id, Category.id_comp,
      uliftSliceUnderIso_hom_val, Category.assoc]
  have hother (b : Fin 2) (hb : b ≠ c) :
      (SSet.uliftFunctor.{u + 1, u}).map
        (nerveMap (alternatingClosedSection κ (toLex (a, c)) b)) ≫
        (U ≫ sliceUnderProjection z) =
      (SSet.uliftFunctor.{u + 1, u}).map
        ((otherComponentIso κ a c b hb).inv ≫ s.stage.index b) ≫ P b := by
    apply (cancel_epi ((SSet.uliftFunctor.{u + 1, u}).map
      (otherComponentIso κ a c b hb).hom)).1
    calc
      _ = (SSet.uliftFunctor.{u + 1, u}).map
          (nerveMap (alternatingLowerSection κ (toLex (a, c)) b)) ≫
          (((SSet.uliftFunctor.{u + 1, u}).map
            (nerveMap (strictPrefixToClosed (toLex (a, c)))) ≫ U) ≫
              sliceUnderProjection z) := rfl
      _ = (SSet.uliftFunctor.{u + 1, u}).map (s.stage.index b) ≫ P b := by
        rw [hold, s.projection, s.stage.component_eq b]
      _ = _ := by
        simp only [CategoryTheory.Functor.map_comp, Category.assoc]
        rw [← Category.assoc ((SSet.uliftFunctor.{u + 1, u}).map
          (otherComponentIso κ a c b hb).hom), ← CategoryTheory.Functor.map_comp,
          Iso.hom_inv_id, (SSet.uliftFunctor.{u + 1, u}).map_id, Category.id_comp]
  let J : ∀ b, nerve (AlternatingComponentClosed κ (toLex (a, c)) b) ⟶ I b := by
    intro b
    by_cases hb : b = c
    · subst b
      exact extendedComponentIndex κ a c j
    · exact (otherComponentIso κ a c b hb).inv ≫ s.stage.index b
  have hJ : ∀ b, (SSet.uliftFunctor.{u + 1, u}).map
      (nerveMap (alternatingClosedSection κ (toLex (a, c)) b)) ≫ (U ≫ sliceUnderProjection z) =
      (SSet.uliftFunctor.{u + 1, u}).map (J b) ≫ P b := by
    intro b
    by_cases hb : b = c
    · subst b
      simpa only [J, dite_true] using hcur
    · simpa only [J, dite_eq_right hb] using hother b hb
  let r : SeededAlternatingClosedStage (κ := κ) (I := I) (P := P) z (toLex (a, c)) :=
    ⟨⟨J, U ≫ sliceUnderProjection z, hJ⟩, U, rfl⟩
  refine ⟨r, ⟨?_, ?_⟩, hold⟩
  · change (SSet.uliftFunctor.{u + 1, u}).map
      (nerveMap (strictPrefixToClosed (toLex (a, c)))) ≫ (U ≫ sliceUnderProjection z) = _
    rw [← Category.assoc, hold, s.projection]
  · intro b
    change nerveMap (alternatingComponentLowerToClosed κ (toLex (a, c)) b) ≫ J b = _
    by_cases hb : b = c
    · subst b
      simpa only [J, dite_true] using extendedComponentIndex_old κ a c j
    · simp only [J, dite_eq_right hb]
      rw [← otherComponentIso_hom κ a c b hb, Iso.hom_inv_id_assoc]

end SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback
