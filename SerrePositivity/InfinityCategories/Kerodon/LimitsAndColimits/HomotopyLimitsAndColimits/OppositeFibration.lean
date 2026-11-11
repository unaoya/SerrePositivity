module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.KanFibrationTools

/-!
概要：単体集合の反転は Kan fibration を保つ。
方針：反転したホーンの包含を元のホーンの反転と同型で同定し、相対持ち上げ性を移す。
規約：始域・終域の Kan 性を要求せず、全ホーンの相対充填を使う。
使われ方：HTT 4.2.4.1、Kerodon 7.5.3.12（Tag 03B1） の反転した Hom 図式の fibration 条件。

対応節は Kerodon 7.5（Tag 039Y）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits

/-- 概要：Kan fibration の単体集合の反転も Kan fibration。
方針：各ホーンを反転同型で移し、圏同値による lifting property の保存を使う。
規約：モデル構造の因子分解や弱同値を使わない。
使われ方：Kerodon 7.5.3.12（Tag 03B1） の cospan と塔の Hom 係数の反転。 -/
instance fibration_opFunctor_map {X Y : SSet.{u}} (p : X ⟶ Y) [Fibration p] :
    Fibration (SSet.opFunctor.map p) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.fibration_of_hasLiftingProperty_horn
  intro n i
  let e : Arrow.mk (horn (n + 1) i.rev.rev).ι ≅
      Arrow.mk (SSet.opFunctor.map (horn (n + 1) i.rev).ι) :=
    Arrow.isoMk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.hornReverseIso (n + 1) i.rev) (stdSimplex.opIso ⦋n + 1⦌).symm
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.hornReverseIso_hom_ι (n + 1) i.rev)
  have : SSet.opFunctor.{u}.IsEquivalence := SSet.opEquivalence.isEquivalence_functor
  have h : HasLiftingProperty (horn (n + 1) i.rev.rev).ι (SSet.opFunctor.map p) := by
    apply (HasLiftingProperty.iff_of_arrow_iso_left e _).mpr
    apply (SSet.opFunctor.hasLiftingProperty_iff_of_isEquivalence _ _).mpr
    exact ((SSet.modelCategoryQuillen.fibration_iff p).mp inferInstance) _
      (horn_ι_mem_J _ i.rev)
  exact (congrArg (fun k : Fin (n + 2) ↦
    HasLiftingProperty (horn (n + 1) k).ι (SSet.opFunctor.map p)) (Fin.rev_rev i)).mp h

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
