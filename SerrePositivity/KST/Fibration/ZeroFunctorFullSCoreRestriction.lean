module
public import SerrePositivity.KST.Fibration.ZeroFunctorFullSKanFamily
public import SerrePositivity.KST.Fibration.StableSingleSCoreFamily
public import SerrePositivity.KST.SConstruction.CoaugmentedTensorStrengthNaturality

/-!
概要：全 S• 上へ延長した零値関手の全族を、元の K-S• の core 作用へ照合する。
方針：元の core 包含と零値作用を周囲の全 S_n へ戻し、包含の単射性で反映する。
規約：全単体・全パラメータと同じ元の core 作用を保持する。
使われ方：元の Verdier 二胞体の短辺を保つ全 S• 比較の境界照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction
open SerrePositivity.KST.LocalizingInvariants

namespace SerrePositivity.KST.Fibration

/-- 全 S_n 作用を元の core へ制限すると、同じ全零値族の元の K-S• 作用と厳密一致する。 -/
theorem zeroFunctorFullSCoreAction_core (A C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u})
    (n : SimplexCategoryᵒᵖ) :
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (sConstruction n.unop.len A.obj)).ι ▷ zeroFunctorLocus A C) ≫
        zeroFunctorFullSCoreAction A C n.unop.len =
      uncurry (zeroFunctorLocusToStableHom A C ≫
        ((stableMultiSCoreEnrichedDiagram 1).obj (fun _ => n)).map A C) := by
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (sConstruction n.unop.len C.obj)).ι).1
  rw [Category.assoc, zeroFunctorFullSCoreAction_ι,
    stableSingleSCoreFamilyAction_inclusion]
  rw [← Category.assoc (zeroFunctorLocusToStableHom A C),
    zeroFunctorLocusToStableHom_inclusion]
  rfl

/-- 元の全関手族としても、全 S_n への延長の core 制限は同じ元の全 Hom 作用。 -/
theorem zeroFunctorFullSCoreFamily_core (A C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u})
    (n : SimplexCategoryᵒᵖ) :
    zeroFunctorFullSCoreFamily A C n.unop.len ≫
        (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (sConstruction n.unop.len A.obj)).ι).app
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (sConstruction n.unop.len C.obj) : SSet.{u}) =
      zeroFunctorLocusToStableHom A C ≫
        ((stableMultiSCoreEnrichedDiagram 1).obj (fun _ => n)).map A C := by
  apply uncurry_injective
  rw [uncurry_pre_app, zeroFunctorFullSCoreFamily, uncurry_curry]
  exact zeroFunctorFullSCoreAction_core A C n

/-- 任意の元の零値族でも、core 上の同じ全二胞体作用を厳密に回収する。 -/
theorem zeroStableHomFamilyLift_fullS_core {P : SSet.{u}} {A C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}}
    (H : P ⟶ (A ⟶[SSet.{u}] C))
    (hH : ∀ v, StableHomZeroVertex A C (H.app (Opposite.op ⦋0⦌) v))
    (n : SimplexCategoryᵒᵖ) :
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (sConstruction n.unop.len A.obj)).ι ▷ P) ≫
        uncurry (zeroStableHomFamilyLift H hH ≫ zeroFunctorFullSCoreFamily A C n.unop.len) =
      uncurry (H ≫ ((stableMultiSCoreEnrichedDiagram 1).obj (fun _ => n)).map A C) := by
  rw [← uncurry_pre_app, Category.assoc, zeroFunctorFullSCoreFamily_core,
    ← Category.assoc, zeroStableHomFamilyLift_recovery]

/-- 同じ core 円柱の実現を、元の core S 実現座標で直接回収する。 -/
theorem singleCoreFamilyCylinder_coreRealization {A C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}} {P : SSet.{u}}
    (H : P ⟶ (A ⟶[SSet.{u}] C))
    (K : (simplicialSConstruction A.obj ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor) ⋙ tensorRight P ⟶
      simplicialSConstruction C.obj ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor)
    (hK : ∀ n, K.app n =
      uncurry (H ≫ ((stableMultiSCoreEnrichedDiagram 1).obj (fun _ => n)).map A C)) :
    simplicialCylinderDiagonal _ _ P K =
      uncurry (H ≫ coreSingleRealizationEnrichedFunctor.map A C) := by
  have hd := singleCoreFamilyCylinder_diagonal H K hK
  rw [coreSingleSimplicialIso_diagonal_hom, coreSingleSimplicialIso_diagonal_hom] at hd
  rw [coreSingleRealizationFamily_coordinates]
  rw [← hd, ← Category.assoc, ← comp_whiskerRight, Iso.hom_inv_id,
    id_whiskerRight, Category.id_comp]

/-- 元の core S• 包含で制限した、全零値族の同じ全 S• 円柱。 -/
def zeroFunctorFullSCoreRestrictionCylinder (A C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) :
    (simplicialSConstruction A.obj ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor) ⋙
        tensorRight (zeroFunctorLocus A C) ⟶
      simplicialSConstruction C.obj ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor :=
  CategoryTheory.Functor.whiskerRight
    (relativeSimplicialSConstructionCoreInclusion (𝟙 A.obj) ≫
      relativeSimplicialSConstructionInclusion (𝟙 A.obj)) (tensorRight (zeroFunctorLocus A C)) ≫
        zeroFunctorFullSCoreNatTrans A C

/-- 同じ制限円柱の全段は、元の K-S• の全零値 Hom 作用そのもの。 -/
theorem zeroFunctorFullSCoreRestrictionCylinder_app (A C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u})
    (n : SimplexCategoryᵒᵖ) :
    (zeroFunctorFullSCoreRestrictionCylinder A C).app n =
      uncurry (zeroFunctorLocusToStableHom A C ≫
        ((stableMultiSCoreEnrichedDiagram 1).obj (fun _ => n)).map A C) := by
  change (((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (sConstruction n.unop.len A.obj)).ι) ▷ _) ≫
    zeroFunctorFullSCoreAction A C n.unop.len = _
  exact zeroFunctorFullSCoreAction_core A C n

/-- 元の core S• から全 S• への、同じ包含の実対角射。 -/
def coreSFullRealizationInclusion (A : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) :
    (coreSingleRealizationObject A).obj ⟶
      simplicialDiagonalFunctor.obj (simplicialSConstruction A.obj) :=
  simplicialDiagonalFunctor.map
    (relativeSimplicialSConstructionCoreInclusion (𝟙 A.obj) ≫
      relativeSimplicialSConstructionInclusion (𝟙 A.obj))

/-- 全 S• の同じ全零値族は、core 実現上で元の全豊穣実現族に厳密一致する。 -/
theorem zeroFunctorFullSCoreRestriction_diagonal (A C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) :
    (coreSFullRealizationInclusion A ▷ zeroFunctorLocus A C) ≫
        simplicialCylinderDiagonal _ _ (zeroFunctorLocus A C) (zeroFunctorFullSCoreNatTrans A C) =
      uncurry (zeroFunctorLocusToStableHom A C ≫ coreSingleRealizationEnrichedFunctor.map A C) := by
  have hd := singleCoreFamilyCylinder_coreRealization (zeroFunctorLocusToStableHom A C)
    (zeroFunctorFullSCoreRestrictionCylinder A C)
    (zeroFunctorFullSCoreRestrictionCylinder_app A C)
  rw [zeroFunctorFullSCoreRestrictionCylinder, simplicialCylinderDiagonal_precomp] at hd
  exact hd

/-- Ex∞ の全 Hom でも、同じ全 S• 延長の core 制限は元の全 Kan Hom 作用そのもの。 -/
theorem zeroFunctorFullSKanFamily_core (A C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) :
    zeroFunctorFullSKanFamily A C ≫
        (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map (coreSFullRealizationInclusion A))).app
          (stableCoreSingleKanObject C).obj =
      zeroFunctorLocusToStableHom A C ≫ stableCoreSingleKanEnrichedFunctor.map A C := by
  apply uncurry_injective
  rw [uncurry_pre_app, zeroFunctorFullSKanFamily_action, ← Category.assoc,
    coaugmentedTensorRightStrength_naturality, Category.assoc, ← Functor.map_comp,
    zeroFunctorFullSCoreRestriction_diagonal]
  exact (stableCoreSingleKanFamily_action (zeroFunctorLocusToStableHom A C)).symm

/-- 元の任意の零値全族の全 Ex∞ 評価を、同じ core 包含後に厳密に回収する。 -/
theorem zeroStableHomFamilyLift_fullSKan_core {P : SSet.{u}} {A C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}}
    (H : P ⟶ (A ⟶[SSet.{u}] C))
    (hH : ∀ v, StableHomZeroVertex A C (H.app (Opposite.op ⦋0⦌) v)) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map (coreSFullRealizationInclusion A) ▷ P) ≫
        uncurry (zeroStableHomFamilyLift H hH ≫ zeroFunctorFullSKanFamily A C) =
      uncurry (H ≫ stableCoreSingleKanEnrichedFunctor.map A C) := by
  rw [← uncurry_pre_app, Category.assoc, zeroFunctorFullSKanFamily_core,
    ← Category.assoc, zeroStableHomFamilyLift_recovery]

end SerrePositivity.KST.Fibration
