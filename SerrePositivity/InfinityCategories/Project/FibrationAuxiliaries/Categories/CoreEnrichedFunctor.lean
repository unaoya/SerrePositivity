module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CoreProduct

/-!
概要：元の相対作用の豊穣関手を、Hom の core を取る豊穣関手へ移す。
方針：各 Hom の射に core 関手を適用し、同じ単位・合成の等式を各単体の値で回収する。
規約：通常の関手や対象ごとの作用だけへの弱めは行わない。
使われ方：cocartesian section の豊穣評価を QCat 値の豊穣関手として実現する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories

/-- 全高次の豊穣作用は、両側で Hom の core を取っても同じ単位・合成を保つ。 -/
def quasicategoryCoreEnrichedFunctor {C : Type v} {D : Type w}
    [EnrichedCategory SSet.{u} C] [EnrichedCategory SSet.{u} D]
    (F : EnrichedFunctor SSet.{u} C D) :
    EnrichedFunctor SSet.{u} (TransportEnrichment _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor.{u} C)
      (TransportEnrichment _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor.{u} D) where
  obj := F.obj
  map X Y := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap (F.map X Y)
  map_id X := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    apply Subtype.ext
    exact congrArg (fun k ↦ k.app n s) (F.map_id X)
  map_comp X Y Z := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    rintro ⟨f, g⟩
    apply Subtype.ext
    exact congrArg (fun k ↦ k.app n (f.val, g.val)) (F.map_comp X Y Z)

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories
