module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.LiftedIntervalFlip
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.DiagramCommaPrismPoint

/-!
概要：元の射図式 comma の円柱を、同じ標準区間を右因子とする円柱にする。
方針：区間の宇宙同型と因子交換を使い、元の三つの全境界を計算する。
規約：元の全試験族と C 側の全図式を保持。使われ方：終点 slice の円柱持ち上げ。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
variable (κ : Cardinal.{u}) {C : SSet.{u}} [Quasicategory C]
  (D : (SSet.uliftFunctor.{u + 1, u}).obj (Δ[1] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity κ C)
  {T : SSet.{u + 1}} (q : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramComma κ D)

/-- 元の C の全射図式を、同じ標準区間上の全パラメーター族として読む。 -/
def indArrowOriginalFamily : T ⊗ (Δ[1] : SSet.{u + 1}) ⟶
    (SSet.uliftFunctor.{u + 1, u}).obj C :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.liftedIntervalFlip T ≫ uncurry (q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramCommaProjection κ D ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftFunctorSpaceIso (Δ[1] : SSet.{u}) C).hom)

/-- 元の全円柱を標準区間へ戻して因子を交換する。 -/
def indArrowNormalizedPrism : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join T (Δ[0] : SSet.{u + 1}) ⊗ Δ[1] ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity κ C :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.liftedIntervalFlip (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join T Δ[0]) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramCommaPrism κ D q

/-- 元の試験族側では、同じ元の C 全図式の Yoneda 像に厳密に一致する。 -/
lemma indArrowNormalizedPrism_old :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl T (Δ[0] : SSet.{u + 1}) ▷ Δ[1]) ≫ indArrowNormalizedPrism κ D q =
      indArrowOriginalFamily κ D q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda κ C := by
  rw [indArrowNormalizedPrism, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.liftedIntervalFlip_naturality,
    Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramCommaPrism_old]
  rfl

/-- 終端側面は、元の指定図式の同じ標準区間表示。 -/
lemma indArrowNormalizedPrism_tip :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr T (Δ[0] : SSet.{u + 1}) ▷ Δ[1]) ≫ indArrowNormalizedPrism κ D q =
      snd (Δ[0] : SSet.{u + 1}) Δ[1] ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.liftedIntervalToSmall ≫ D) := by
  rw [indArrowNormalizedPrism, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.liftedIntervalFlip_naturality,
    Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramCommaPrism_tip, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.liftedIntervalFlip_fst,
    Category.assoc]

/-- 始点では、同じ q の元の全余錐の始点評価になる。 -/
lemma indArrowNormalizedPrism_first :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join T (Δ[0] : SSet.{u + 1}) ◁ stdSimplex.δ 1) ≫ indArrowNormalizedPrism κ D q =
      fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join T Δ[0]) (Δ[0] : SSet.{u + 1}) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap q (𝟙 Δ[0]) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramCommaCocone κ D).val ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (ULift.up (stdSimplex.obj₀Equiv.{u}.symm (0 : Fin 2))) := by
  rw [indArrowNormalizedPrism, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.liftedIntervalFlip_first, Category.assoc]
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.curry_evaluateFunctorAt_vertex (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramCommaPrism κ D q)
    (ULift.up (stdSimplex.obj₀Equiv.{u}.symm (0 : Fin 2)))
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramCommaPrism, curry_uncurry] at h
  simpa only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramCommaPrism] using congrArg (fun f =>
    fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join T (Δ[0] : SSet.{u + 1})) Δ[0] ≫ f) h.symm

/-- 元の C 値関手空間の宇宙比較は、元の同じ頂点での評価を保つ。 -/
lemma indArrowFunctorSpace_evaluate (k : (Δ[1] : SSet.{u}) _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftFunctorSpaceIso (Δ[1] : SSet.{u}) C).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (ULift.up k) =
      (SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := C) k) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  rfl

/-- 元の C 側の始点は、元の試験族の同じ評価そのもの。 -/
lemma indArrowOriginalFamily_first : (T ◁ stdSimplex.δ 1) ≫ indArrowOriginalFamily κ D q =
    fst T (Δ[0] : SSet.{u + 1}) ≫ q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramCommaProjection κ D ≫
      (SSet.uliftFunctor.{u + 1, u}).map
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := C) (stdSimplex.obj₀Equiv.{u}.symm (0 : Fin 2))) := by
  rw [indArrowOriginalFamily, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.liftedIntervalFlip_first, Category.assoc]
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.curry_evaluateFunctorAt_vertex (uncurry (q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramCommaProjection κ D ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftFunctorSpaceIso (Δ[1] : SSet.{u}) C).hom))
      (ULift.up (stdSimplex.obj₀Equiv.{u}.symm (0 : Fin 2)))
  rw [curry_uncurry] at h
  simp only [Category.assoc, indArrowFunctorSpace_evaluate] at h
  simpa only [Category.assoc] using congrArg (fun f => fst T (Δ[0] : SSet.{u + 1}) ≫ f) h.symm

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
