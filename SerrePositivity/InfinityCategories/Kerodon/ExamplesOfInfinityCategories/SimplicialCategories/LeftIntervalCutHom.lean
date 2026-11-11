module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.LeftPrismCutMinimumMaps
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.LeftIntervalWeightedSimplex

/-!
概要：左区間の混合 Hom を、同じ weighted cone の切断後のパラメーターへ戻す。
方針：thickening の切断の像を端点の等式で正規化し、path の最小点の一致を使う。
規約：元の左区間の実際の Hom の作用を保持し、正規化の同型を明示する。
使われ方：weighted pointed prism の正頂点間の Hom と初点からの係数の合成則。

対応節は Kerodon 2.4（Tag 00JN）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SimplicialThickening SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories


/-- 元の左切断の豊穣 Hom の作用は、端点を揃えると同じ path の像の nerve。 -/
lemma thickeningLeftPrismCut_map {n : ℕ} (t : Fin (n + 1) →o Fin 2)
    (i j : Fin (n + 1)) (hi : t i = 0) (hj : t j = 1) :
    (SimplicialThickening.functor (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.coherentLeftPrismCut t).uliftMap).map
      (⟨ULift.up i⟩ : SimplicialThickening (ULift.{u} (Fin (n + 1)))) ⟨ULift.up j⟩ ≫
      eqToHom (congrArg₂ (fun a b : Fin (n + 2) => SimplicialCategory.sHom
        (⟨ULift.up a⟩ : SimplicialThickening (ULift.{u} (Fin (n + 2)))) ⟨ULift.up b⟩)
        (show _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.coherentLeftPrismCut t i = 0 from ite_eq_left hi)
        (show _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.coherentLeftPrismCut t j = j.succ from ite_eq_right (by rw [hj]; decide))) =
    nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.leftPrismCutPathFunctor t i j hi hj) := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro P
  apply CategoryTheory.Functor.ext (fun k => ?_)
  apply SimplicialThickening.Path.ext
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.thickeningHom_transport_I
    (congrArg (fun a : Fin (n + 2) =>
      (⟨ULift.up a⟩ : SimplicialThickening (ULift.{u} (Fin (n + 2)))))
      (show _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.coherentLeftPrismCut t i = 0 from ite_eq_left hi))
    (congrArg (fun a : Fin (n + 2) =>
      (⟨ULift.up a⟩ : SimplicialThickening (ULift.{u} (Fin (n + 2)))))
      (show _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.coherentLeftPrismCut t j = j.succ from ite_eq_right (by rw [hj]; decide)))
    (((SimplicialThickening.functor (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.coherentLeftPrismCut t).uliftMap).map
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
    (τ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixWeight n ⟶ σ ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F x ⋙ SSet.opFunctor)
    {a b a' b' : Fin (n + 2)} (ha : a = a') (hb : b = b') {X Y : C}
    (hX : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeObj x (σ ⋙ F) a' = X) (hY : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeObj x (σ ⋙ F) b' = Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeHom F x τ a b ≫ eqToHom (congrArg₂ SimplicialCategory.sHom
      ((congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeObj x (σ ⋙ F)) ha).trans hX)
      ((congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeObj x (σ ⋙ F)) hb).trans hY)) =
    eqToHom (congrArg₂ (fun p q : Fin (n + 2) => SimplicialCategory.sHom
      (⟨ULift.up p⟩ : SimplicialThickening (ULift.{u} (Fin (n + 2)))) ⟨ULift.up q⟩) ha hb) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeHom F x τ a' b' ≫ eqToHom (congrArg₂ SimplicialCategory.sHom hX hY) := by
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
  (((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentLeftHomInterval x (F.obj i)).app (Opposite.op ⦋n⦌)
    (t, (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.uliftOppositeIso (SimplicialCategory.sHom x (F.obj i))).hom.app _ (ULift.up s))).map
      ⟨ULift.up a⟩ ⟨ULift.up b⟩) ≫
    eqToHom (congrArg₂ SimplicialCategory.sHom
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentLeftHomInterval_obj_zero F x i s t a ha)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentLeftHomInterval_obj_one F x i s t b hb))

/-- 元の左区間の混合 Hom は、weighted cone と同じ切断後の係数の全評価。 -/
lemma coherentLeftHomIntervalMixedHom_eq_cut {I : Type u} [SmallCategory I]
    {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (F : I ⥤ C) (x : C) (i : I) {n : ℕ}
    (s : (SimplicialCategory.sHom x (F.obj i)).op _⦋n⦌)
    (t : (Δ[1] : SSet.{max u v}) _⦋n⦌) (a b : Fin (n + 1))
    (ha : (stdSimplex.objEquiv t).toOrderHom a = 0)
    (hb : (stdSimplex.objEquiv t).toOrderHom b = 1) :
    coherentLeftHomIntervalMixedHom F x i s t a b ha hb =
      nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.pathPositiveShiftFunctor a b) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutMinimumMap (stdSimplex.objEquiv t).toOrderHom hb ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.reflectedSimplexMap (SSet.yonedaEquiv.symm s) := by
  let τ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveConstantDiagram (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F x ⋙ SSet.opFunctor) i s
  let c := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.coherentLeftPrismCut (stdSimplex.objEquiv t).toOrderHom
  have h0 : c a = 0 := ite_eq_left ha
  have h1 : c b = b.succ := ite_eq_right (by rw [hb]; decide)
  let T := (SimplicialThickening.functor c.uliftMap).comp SSet (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeSimplex F x τ)
  have hs : ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentLeftHomInterval x (F.obj i)).app (Opposite.op ⦋n⦌)
      (t, (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.uliftOppositeIso (SimplicialCategory.sHom x (F.obj i))).hom.app _ (ULift.up s))) = T :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentLeftHomInterval_weightedConstantCone F x i s t
  have hT0 : T.obj ⟨ULift.up a⟩ = x := by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeObj x _ (c a) = x
    rw [h0]
    rfl
  have hT1 : T.obj ⟨ULift.up b⟩ = F.obj i := by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeObj x _ (c b) = F.obj i
    rw [h1]
    rfl
  unfold coherentLeftHomIntervalMixedHom
  rw [normalizedEnrichedMap_eq _ T hs _ _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentLeftHomInterval_obj_zero F x i s t a ha)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentLeftHomInterval_obj_one F x i s t b hb) hT0 hT1]
  change (((SimplicialThickening.functor c.uliftMap).map
    (⟨ULift.up a⟩ : SimplicialThickening (ULift.{u} (Fin (n + 1)))) ⟨ULift.up b⟩) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeHom F x τ (c a) (c b)) ≫ _ = _
  rw [Category.assoc, weightedConeHom_transport F x τ h0 h1 rfl rfl]
  simp only [eqToHom_refl, Category.comp_id, ← Category.assoc]
  rw [thickeningLeftPrismCut_map]
  change nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.leftPrismCutPathFunctor (stdSimplex.objEquiv t).toOrderHom a b ha hb) ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.pathFirstMinimumMap b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.reflectedSimplexMap
      (stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion b.val n (by omega)) ≫ SSet.yonedaEquiv.symm s)) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.reflectedSimplexMap_pre]
  simpa only [Category.assoc] using
    (congrArg (fun f => f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.reflectedSimplexMap (SSet.yonedaEquiv.symm s))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.pathCutMinimumMap_eq_leftPrismCut (stdSimplex.objEquiv t).toOrderHom a b ha hb)).symm

/-- 時刻零同士の元の左区間の Hom は、始点の豊穣単位を定値にした射。 -/
lemma coherentLeftHomIntervalHom_zero {I : Type u} [SmallCategory I]
    {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (F : I ⥤ C) (x : C) (i : I) {n : ℕ}
    (s : (SimplicialCategory.sHom x (F.obj i)).op _⦋n⦌)
    (t : (Δ[1] : SSet.{max u v}) _⦋n⦌) (a b : Fin (n + 1))
    (ha : (stdSimplex.objEquiv t).toOrderHom a = 0)
    (hb : (stdSimplex.objEquiv t).toOrderHom b = 0) :
    (((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentLeftHomInterval x (F.obj i)).app (Opposite.op ⦋n⦌)
      (t, (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.uliftOppositeIso (SimplicialCategory.sHom x (F.obj i))).hom.app _ (ULift.up s))).map
        ⟨ULift.up a⟩ ⟨ULift.up b⟩) ≫
      eqToHom (congrArg₂ SimplicialCategory.sHom
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentLeftHomInterval_obj_zero F x i s t a ha)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentLeftHomInterval_obj_zero F x i s t b hb)) =
      SemiCartesianMonoidalCategory.toUnit _ ≫ eId SSet x := by
  let τ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveConstantDiagram (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F x ⋙ SSet.opFunctor) i s
  let c := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.coherentLeftPrismCut (stdSimplex.objEquiv t).toOrderHom
  have h0 : c a = 0 := ite_eq_left ha
  have h1 : c b = 0 := ite_eq_left hb
  let T := (SimplicialThickening.functor c.uliftMap).comp SSet (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeSimplex F x τ)
  have hs : ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentLeftHomInterval x (F.obj i)).app (Opposite.op ⦋n⦌)
      (t, (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.uliftOppositeIso (SimplicialCategory.sHom x (F.obj i))).hom.app _ (ULift.up s))) = T :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentLeftHomInterval_weightedConstantCone F x i s t
  have hT0 : T.obj ⟨ULift.up a⟩ = x := by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeObj x _ (c a) = x
    rw [h0]
    rfl
  have hT1 : T.obj ⟨ULift.up b⟩ = x := by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeObj x _ (c b) = x
    rw [h1]
    rfl
  rw [normalizedEnrichedMap_eq _ T hs _ _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentLeftHomInterval_obj_zero F x i s t a ha)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentLeftHomInterval_obj_zero F x i s t b hb) hT0 hT1]
  change (((SimplicialThickening.functor c.uliftMap).map
    (⟨ULift.up a⟩ : SimplicialThickening (ULift.{u} (Fin (n + 1)))) ⟨ULift.up b⟩) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeHom F x τ (c a) (c b)) ≫ _ = _
  rw [Category.assoc, weightedConeHom_transport F x τ h0 h1 rfl rfl]
  simp only [eqToHom_refl, Category.comp_id]
  change _ ≫ (SemiCartesianMonoidalCategory.toUnit _ ≫ eId SSet x) = _
  simp only [← Category.assoc, SemiCartesianMonoidalCategory.comp_toUnit]

/-- 時刻一同士の元の左区間の Hom は、終点の豊穣単位を定値にした射。 -/
lemma coherentLeftHomIntervalHom_one {I : Type u} [SmallCategory I]
    {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (F : I ⥤ C) (x : C) (i : I) {n : ℕ}
    (s : (SimplicialCategory.sHom x (F.obj i)).op _⦋n⦌)
    (t : (Δ[1] : SSet.{max u v}) _⦋n⦌) (a b : Fin (n + 1))
    (ha : (stdSimplex.objEquiv t).toOrderHom a = 1)
    (hb : (stdSimplex.objEquiv t).toOrderHom b = 1) :
    (((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentLeftHomInterval x (F.obj i)).app (Opposite.op ⦋n⦌)
      (t, (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.uliftOppositeIso (SimplicialCategory.sHom x (F.obj i))).hom.app _ (ULift.up s))).map
        ⟨ULift.up a⟩ ⟨ULift.up b⟩) ≫
      eqToHom (congrArg₂ SimplicialCategory.sHom
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentLeftHomInterval_obj_one F x i s t a ha)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentLeftHomInterval_obj_one F x i s t b hb)) =
      SemiCartesianMonoidalCategory.toUnit _ ≫ eId SSet (F.obj i) := by
  let τ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveConstantDiagram (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F x ⋙ SSet.opFunctor) i s
  let c := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.coherentLeftPrismCut (stdSimplex.objEquiv t).toOrderHom
  have h0 : c a = a.succ := ite_eq_right (by rw [ha]; decide)
  have h1 : c b = b.succ := ite_eq_right (by rw [hb]; decide)
  let T := (SimplicialThickening.functor c.uliftMap).comp SSet (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeSimplex F x τ)
  have hs : ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentLeftHomInterval x (F.obj i)).app (Opposite.op ⦋n⦌)
      (t, (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.uliftOppositeIso (SimplicialCategory.sHom x (F.obj i))).hom.app _ (ULift.up s))) = T :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentLeftHomInterval_weightedConstantCone F x i s t
  have hT0 : T.obj ⟨ULift.up a⟩ = F.obj i := by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeObj x _ (c a) = F.obj i
    rw [h0]
    rfl
  have hT1 : T.obj ⟨ULift.up b⟩ = F.obj i := by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeObj x _ (c b) = F.obj i
    rw [h1]
    rfl
  have hTail : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeHom F x τ a.succ b.succ =
      SemiCartesianMonoidalCategory.toUnit _ ≫ eId SSet (F.obj i) := by
    apply SSet.hom_ext
    rintro ⟨⟨d⟩⟩
    apply ConcreteCategory.hom_ext
    intro P
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (SimplicialCategory.homEquiv' _ _ (F.map (𝟙 i))) d =
      (eId SSet (F.obj i)).app (Opposite.op ⦋d⦌) PUnit.unit
    rw [F.map_id]
    simp only [SimplicialCategory.homEquiv', Equiv.trans_apply, eHomEquiv_id]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.unitHom_app_constant (eId SSet (F.obj i)) d).symm
  rw [normalizedEnrichedMap_eq _ T hs _ _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentLeftHomInterval_obj_one F x i s t a ha)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentLeftHomInterval_obj_one F x i s t b hb) hT0 hT1]
  change (((SimplicialThickening.functor c.uliftMap).map
    (⟨ULift.up a⟩ : SimplicialThickening (ULift.{u} (Fin (n + 1)))) ⟨ULift.up b⟩) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeHom F x τ (c a) (c b)) ≫ _ = _
  rw [Category.assoc, weightedConeHom_transport F x τ h0 h1 rfl rfl]
  simp only [eqToHom_refl, Category.comp_id]
  rw [hTail]
  simp only [← Category.assoc]
  apply congrArg (fun f => f ≫ eId SSet (F.obj i))
  exact Subsingleton.elim _ _

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
