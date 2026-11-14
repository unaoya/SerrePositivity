module
public import SerrePositivity.KST.SConstruction.StableMultiSCoreDiagram
public import SerrePositivity.KST.Fibration.ZeroEndPostcompSAction

/-! # 元の一回の core S• の全 Kan Hom 作用と、同じ全 S_n 作用の包含後の照合 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration

/-- 一回の元の S• の全 Kan 入力族は、同じ全完全関手族の S_n 作用である。 -/
theorem stableSingleSFullFamily (n : SimplexCategoryᵒᵖ) (A C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) :
    ((stableMultiSEnrichedDiagram 1).obj (fun _ => n)).map A C =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors A C : SSet.{u})).ι ≫
        sExactFamilyMap n.unop.len A C := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors A C : SSet.{u})).ι ≫
    (multiSQuasicategoryEnrichedFunctor 1 (fun _ => n)).map A C = _
  rw [multiSQuasicategoryEnrichedFunctor_map_succ]
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors A C : SSet.{u})).ι ≫
    (𝟙 (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors A C : SSet.{u}) ≫ sExactFamilyMap n.unop.len A C) = _
  rw [Category.id_comp]

/-- 元の一回の core S• の全族は、包含後に同じ S_n 全族の core 制限を回収する。 -/
theorem stableSingleSCoreFamily_inclusion (n : SimplexCategoryᵒᵖ)
    (A C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) :
    ((stableMultiSCoreEnrichedDiagram 1).obj (fun _ => n)).map A C ≫
        (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (sConstruction n.unop.len A.obj) : SSet.{u})).map
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (sConstruction n.unop.len C.obj)).ι =
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors A C : SSet.{u})).ι ≫
        sExactFamilyMap n.unop.len A C) ≫
          (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (sConstruction n.unop.len A.obj)).ι).app
            (sConstruction n.unop.len C.obj) := by
  have h := quasicategoryEnrichedCoreFunctor_inclusion
    ((stableMultiSEnrichedDiagram 1).obj (fun _ => n)) A C
  rw [stableSingleSFullFamily] at h
  change ((quasicategoryEnrichedCoreFunctor
    ((stableMultiSEnrichedDiagram 1).obj (fun _ => n))).map A C ≫ 𝟙 _) ≫ _ = _
  rw [Category.comp_id]
  exact h

/-- 同じ任意の入力族の実 core S_n 作用を、元の全 S_n 作用へ読み戻す。 -/
theorem stableSingleSCoreFamilyAction_inclusion {T : SSet.{u}}
    {A C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}} (H : T ⟶ (A ⟶[SSet.{u}] C)) (n : SimplexCategoryᵒᵖ) :
    uncurry (H ≫ ((stableMultiSCoreEnrichedDiagram 1).obj (fun _ => n)).map A C) ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (sConstruction n.unop.len C.obj)).ι =
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (sConstruction n.unop.len A.obj)).ι ▷ T) ≫
        uncurry (H ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors A C : SSet.{u})).ι ≫
          sExactFamilyMap n.unop.len A C) := by
  have h := congrArg (H ≫ ·) (stableSingleSCoreFamily_inclusion n A C)
  rw [← Category.assoc, ← Category.assoc] at h
  have hu := congrArg (uncurry (C := SSet.{u})) h
  rw [uncurry_natural_right, uncurry_pre_app] at hu
  exact hu

/-- 同じ零値後合成円柱の元の core S_n 作用は、包含後に元の全円柱を回収する。 -/
theorem zeroEndPostcompCoreSAction_inclusion {A C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}} (F : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A C)
    (hF : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F.hom)) (n : SimplexCategoryᵒᵖ) :
    uncurry (zeroEndPostcompFamily F hF ≫
        ((stableMultiSCoreEnrichedDiagram 1).obj (fun _ => n)).map A C) ≫
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (sConstruction n.unop.len C.obj)).ι =
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (sConstruction n.unop.len A.obj)).ι ▷ (Δ[1] : SSet.{u})) ≫
        zeroEndPostcompSAction F hF n.unop.len :=
  stableSingleSCoreFamilyAction_inclusion _ _

end SerrePositivity.KST.Fibration
