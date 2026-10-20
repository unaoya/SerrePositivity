module

public import SerrePositivity.InfinityCategories.F1.LeftPrismCutMinimumMaps
public import SerrePositivity.InfinityCategories.F1.CoherentLeftIntervalWeightedSimplex

/-!
概要：左区間の混合 Hom を、同じ weighted cone の切断後のパラメーターへ戻す。
方針：thickening の切断の像を端点の等式で正規化し、path の最小点の一致を使う。
規約：元の左区間の実際の Hom の作用を保持し、正規化の同型を明示する。
使われ方：weighted pointed prism の正頂点間の Hom と初点からの係数の合成則。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SimplicialThickening SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
open HomotopyLimits

/-- 元の左切断の豊穣 Hom の作用は、端点を揃えると同じ path の像の nerve。 -/
lemma thickeningLeftPrismCut_map {n : ℕ} (t : Fin (n + 1) →o Fin 2)
    (i j : Fin (n + 1)) (hi : t i = 0) (hj : t j = 1) :
    (SimplicialThickening.functor (coherentLeftPrismCut t).uliftMap).map
      (⟨ULift.up i⟩ : SimplicialThickening (ULift.{u} (Fin (n + 1)))) ⟨ULift.up j⟩ ≫
      eqToHom (congrArg₂ (fun a b : Fin (n + 2) => SimplicialCategory.sHom
        (⟨ULift.up a⟩ : SimplicialThickening (ULift.{u} (Fin (n + 2)))) ⟨ULift.up b⟩)
        (show coherentLeftPrismCut t i = 0 from ite_eq_left hi)
        (show coherentLeftPrismCut t j = j.succ from ite_eq_right (by rw [hj]; decide))) =
    nerveMap (leftPrismCutPathFunctor t i j hi hj) := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro P
  apply CategoryTheory.Functor.ext (fun k => ?_)
  apply SimplicialThickening.Path.ext
  have h := thickeningHom_transport_I
    (congrArg (fun a : Fin (n + 2) =>
      (⟨ULift.up a⟩ : SimplicialThickening (ULift.{u} (Fin (n + 2)))))
      (show coherentLeftPrismCut t i = 0 from ite_eq_left hi))
    (congrArg (fun a : Fin (n + 2) =>
      (⟨ULift.up a⟩ : SimplicialThickening (ULift.{u} (Fin (n + 2)))))
      (show coherentLeftPrismCut t j = j.succ from ite_eq_right (by rw [hj]; decide)))
    (((SimplicialThickening.functor (coherentLeftPrismCut t).uliftMap).map
      (⟨ULift.up i⟩ : SimplicialThickening (ULift.{u} (Fin (n + 1)))) ⟨ULift.up j⟩).app d P) k
  exact h

private lemma normalizedEnrichedMap_eq {A : Type u} [Category.{u} A]
    [SimplicialCategory A] {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (R T : EnrichedFunctor SSet.{u} A C) (h : R = T) (a b : A) {X Y : C}
    (ha : R.obj a = X) (hb : R.obj b = Y) (ha' : T.obj a = X) (hb' : T.obj b = Y) :
    R.map a b ≫ eqToHom (congrArg₂ SimplicialCategory.sHom ha hb) =
      T.map a b ≫ eqToHom (congrArg₂ SimplicialCategory.sHom ha' hb') := by
  subst T
  rfl

private lemma weightedConeHom_transport {I : Type u} [SmallCategory I]
    {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (F : I ⥤ C) (x : C) {n : ℕ} {σ : ComposableArrows I n}
    (τ : simplexPrefixWeight n ⟶ σ ⋙ simplicialHomDiagram F x ⋙ SSet.opFunctor)
    {a b a' b' : Fin (n + 2)} (ha : a = a') (hb : b = b') {X Y : C}
    (hX : weightedConeObj x (σ ⋙ F) a' = X) (hY : weightedConeObj x (σ ⋙ F) b' = Y) :
    weightedConeHom F x τ a b ≫ eqToHom (congrArg₂ SimplicialCategory.sHom
      ((congrArg (weightedConeObj x (σ ⋙ F)) ha).trans hX)
      ((congrArg (weightedConeObj x (σ ⋙ F)) hb).trans hY)) =
    eqToHom (congrArg₂ (fun p q : Fin (n + 2) => SimplicialCategory.sHom
      (⟨ULift.up p⟩ : SimplicialThickening (ULift.{u} (Fin (n + 2)))) ⟨ULift.up q⟩) ha hb) ≫
    weightedConeHom F x τ a' b' ≫ eqToHom (congrArg₂ SimplicialCategory.sHom hX hY) := by
  subst a'
  subst b'
  simp

/-- 左区間の実際の混合 Hom を、始点・終点の標準表示に揃える。 -/
def coherentLeftHomIntervalMixedHom {I : Type u} [SmallCategory I]
    {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (F : I ⥤ C) (x : C) (i : I) {n : ℕ}
    (s : (SimplicialCategory.sHom x (F.obj i)).op _⦋n⦌)
    (t : (Δ[1] : SSet.{max u v}) _⦋n⦌) (a b : Fin (n + 1))
    (ha : (stdSimplex.objEquiv t).toOrderHom a = 0)
    (hb : (stdSimplex.objEquiv t).toOrderHom b = 1) :
    SimplicialCategory.sHom
      (⟨ULift.up a⟩ : SimplicialThickening (ULift.{u} (Fin (n + 1)))) ⟨ULift.up b⟩ ⟶
      SimplicialCategory.sHom x (F.obj i) :=
  (((coherentLeftHomInterval x (F.obj i)).app (Opposite.op ⦋n⦌)
    (t, (uliftOppositeIso (SimplicialCategory.sHom x (F.obj i))).hom.app _ (ULift.up s))).map
      ⟨ULift.up a⟩ ⟨ULift.up b⟩) ≫
    eqToHom (congrArg₂ SimplicialCategory.sHom
      (coherentLeftHomInterval_obj_zero F x i s t a ha)
      (coherentLeftHomInterval_obj_one F x i s t b hb))

/-- 元の左区間の混合 Hom は、weighted cone と同じ切断後の係数の全評価。 -/
lemma coherentLeftHomIntervalMixedHom_eq_cut {I : Type u} [SmallCategory I]
    {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (F : I ⥤ C) (x : C) (i : I) {n : ℕ}
    (s : (SimplicialCategory.sHom x (F.obj i)).op _⦋n⦌)
    (t : (Δ[1] : SSet.{max u v}) _⦋n⦌) (a b : Fin (n + 1))
    (ha : (stdSimplex.objEquiv t).toOrderHom a = 0)
    (hb : (stdSimplex.objEquiv t).toOrderHom b = 1) :
    coherentLeftHomIntervalMixedHom F x i s t a b ha hb =
      nerveMap (pathPositiveShiftFunctor a b) ≫
        pathCutMinimumMap (stdSimplex.objEquiv t).toOrderHom hb ≫
          reflectedSimplexMap (SSet.yonedaEquiv.symm s) := by
  let τ := weightedNerveConstantDiagram (simplicialHomDiagram F x ⋙ SSet.opFunctor) i s
  let c := coherentLeftPrismCut (stdSimplex.objEquiv t).toOrderHom
  have h0 : c a = 0 := ite_eq_left ha
  have h1 : c b = b.succ := ite_eq_right (by rw [hb]; decide)
  let T := (SimplicialThickening.functor c.uliftMap).comp SSet (weightedConeSimplex F x τ)
  have hs : ((coherentLeftHomInterval x (F.obj i)).app (Opposite.op ⦋n⦌)
      (t, (uliftOppositeIso (SimplicialCategory.sHom x (F.obj i))).hom.app _ (ULift.up s))) = T :=
    coherentLeftHomInterval_weightedConstantCone F x i s t
  have hT0 : T.obj ⟨ULift.up a⟩ = x := by
    change weightedConeObj x _ (c a) = x
    rw [h0]
    rfl
  have hT1 : T.obj ⟨ULift.up b⟩ = F.obj i := by
    change weightedConeObj x _ (c b) = F.obj i
    rw [h1]
    rfl
  unfold coherentLeftHomIntervalMixedHom
  rw [normalizedEnrichedMap_eq _ T hs _ _
    (coherentLeftHomInterval_obj_zero F x i s t a ha)
    (coherentLeftHomInterval_obj_one F x i s t b hb) hT0 hT1]
  change (((SimplicialThickening.functor c.uliftMap).map
    (⟨ULift.up a⟩ : SimplicialThickening (ULift.{u} (Fin (n + 1)))) ⟨ULift.up b⟩) ≫
    weightedConeHom F x τ (c a) (c b)) ≫ _ = _
  rw [Category.assoc, weightedConeHom_transport F x τ h0 h1 rfl rfl]
  simp only [eqToHom_refl, Category.comp_id, ← Category.assoc]
  rw [thickeningLeftPrismCut_map]
  change nerveMap (leftPrismCutPathFunctor (stdSimplex.objEquiv t).toOrderHom a b ha hb) ≫
    (pathFirstMinimumMap b ≫ reflectedSimplexMap
      (stdSimplex.map (simplexPrefixInclusion b.val n (by omega)) ≫ SSet.yonedaEquiv.symm s)) = _
  rw [reflectedSimplexMap_pre]
  simpa only [Category.assoc] using
    (congrArg (fun f => f ≫ reflectedSimplexMap (SSet.yonedaEquiv.symm s))
      (pathCutMinimumMap_eq_leftPrismCut (stdSimplex.objEquiv t).toOrderHom a b ha hb)).symm

end SerrePositivity.InfinityCategories
