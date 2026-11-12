module
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.CoreEnrichedFunctor

/-! # 全 Hom の core から元の豊穣圏への実包含
概要：Hom の実 core を取った豊穣圏から、元の豊穣圏へ同じ対象と全単体を包含する。
方針：元の core 包含と、lax tensor の元の成分を各次数で照合する。
規約：自然同値の高次入力を削除しない。使われ方：完全 Perf 関手族の S• 図式への接続。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet SerrePositivity.InfinityCategories
variable (C : Type v) [EnrichedCategory SSet.{u} C]

/-- 実 core の全 Hom を、同じ元の豊穣 Hom へ含める厳密豊穣関手。 -/
def coreEnrichedInclusion :
    EnrichedFunctor SSet.{u} (TransportEnrichment _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor.{u} C) C where
  obj X := X
  map X Y := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore ((show C from X) ⟶[SSet.{u}] (show C from Y))).ι
  map_id X := by
    ext n p
    rfl
  map_comp X Y Z := by
    ext n p
    rfl

/-- 元の Hom 作用は、同じ全単体の実 core 包含。 -/
lemma coreEnrichedInclusion_map (X Y : TransportEnrichment _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor.{u} C) :
    (coreEnrichedInclusion C).map X Y =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore ((show C from X) ⟶[SSet.{u}] (show C from Y))).ι := rfl

end SerrePositivity.KST.SConstruction
