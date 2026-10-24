module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.StrictTransportFibration
public import SerrePositivity.InfinityCategories.F1.Cocartesian.TransportDiagramMixedHom
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.StrictIntervalMappingPullback

/-!
概要：一次元の元の輸送図式の後合成は、全内部 Hom で同値を持ち上げる。
方針：標的図式の輸送による表示から、薄い底上の持ち上げ条件を回収する。
規約：任意の図式の遷移に充填性を仮定しない。
使われ方：一次元の元の Hom の core を引き戻しとして表示する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
namespace SerrePositivity.InfinityCategories

/-- 元の一次元輸送図式の遷移は、全内部 Hom で同値を右に持ち上げる。 -/
lemma kanEquivalenceLifting_cocartesianIntervalPostHom
    (G : CocartesianTransportDiagramCategory (ULift.{u} (Fin 2))) (A : SSet.{u}) :
    SerrePositivity.InfinityCategories.F1B.EquivalenceLifting ((ihom A).map (G.val.map strictIntervalIndexArrow)) := by
  obtain ⟨q, hq⟩ := G.property
  rw [← hq]
  exact kanEquivalenceLifting_kanCocartesianStrictTransportPostHom q.val.hom
    strictIntervalIndexArrow A

/-- 同じ一次元図式の後合成の実際の core は Kan fibration。 -/
lemma core_cocartesianIntervalPostHom_fibration
    (G : CocartesianTransportDiagramCategory (ULift.{u} (Fin 2))) (A : SSet.{u}) :
    Fibration (quasicategoryCoreMap ((ihom A).map (G.val.map strictIntervalIndexArrow))) :=
  F2.coreMap_fibration_of_kanEquivalenceLifting _
    (kanEquivalenceLifting_cocartesianIntervalPostHom G A)

end SerrePositivity.InfinityCategories
