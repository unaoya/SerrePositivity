module
public import SerrePositivity.KST.Fibration.SimplicialCylinderDiagonal
public import SerrePositivity.KST.SConstruction.SimplicialDiagramDiagonalEnrichedFunctor
public import SerrePositivity.KST.SConstruction.StableMultiRealizationEnrichedFunctor

/-! # 全図式族の実円柱と、元の全反復 core S• の豊穣対角作用の厳密な一致 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.KST.SConstruction
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration

/-- 同じ図式 Hom の全入力族を、全段に自然な実円柱として評価する。 -/
def diagramFamilyCylinder (X Y : SimplicialSSetDiagram.{u}) (P : SSet.{u})
    (H : P ⟶ (X ⟶[SSet.{u}] Y)) : X.diagram ⋙ tensorRight P ⟶ Y.diagram where
  app n := uncurry (H ≫ simplicialSSetDiagramProjection X Y n)
  naturality {_ _} θ := by
    have h := congrArg (H ≫ ·) (simplicialSSetDiagramProjection_naturality X Y θ)
    rw [← Category.assoc, ← Category.assoc] at h
    have hu := congrArg (uncurry (C := SSet.{u})) h
    rw [uncurry_natural_right, uncurry_pre_app] at hu
    exact hu.symm

/-- 元の全族の対角評価は、元の豊穣対角作用の同じ全パラメータ評価と厳密一致。 -/
theorem diagramFamilyCylinder_diagonal (X Y : SimplicialSSetDiagram.{u}) (P : SSet.{u})
    (H : P ⟶ (X ⟶[SSet.{u}] Y)) :
    simplicialCylinderDiagonal X.diagram Y.diagram P (diagramFamilyCylinder X Y P H) =
      uncurry (H ≫ simplicialSSetDiagramDiagonalEnrichedFunctor.map X Y) := by
  change _ = uncurry (H ≫ curry (simplicialSSetDiagramDiagonalAction X Y))
  rw [uncurry_natural_left, uncurry_curry]
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨x, p⟩
  rfl

/-- 指定した各段が同じ Hom 族の作用なら、元の対角円柱も同じ対角作用である。 -/
theorem diagramCylinder_eq_diagonalFamily (X Y : SimplicialSSetDiagram.{u}) (P : SSet.{u})
    (H : P ⟶ (X ⟶[SSet.{u}] Y)) (K : X.diagram ⋙ tensorRight P ⟶ Y.diagram)
    (hK : ∀ n, K.app n = uncurry (H ≫ simplicialSSetDiagramProjection X Y n)) :
    simplicialCylinderDiagonal X.diagram Y.diagram P K =
      uncurry (H ≫ simplicialSSetDiagramDiagonalEnrichedFunctor.map X Y) := by
  have he : K = diagramFamilyCylinder X Y P H := NatTrans.ext (funext hK)
  rw [he]
  exact diagramFamilyCylinder_diagonal X Y P H

/-- 元の安定圏の任意の入力族を、同じ全反復 core S• の全円柱へ送る。 -/
def stableMultiCoreFamilyCylinder (r : ℕ) {A C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}} {P : SSet.{u}}
    (H : P ⟶ (A ⟶[SSet.{u}] C)) :
    ((stableMultiSCoreObjectEnrichedFunctor r).obj A).diagram ⋙ tensorRight P ⟶
      ((stableMultiSCoreObjectEnrichedFunctor r).obj C).diagram :=
  diagramFamilyCylinder _ _ P (H ≫ (stableMultiSCoreObjectEnrichedFunctor r).map A C)

/-- 元の全反復 core 族の各段は、同じ入力族の同じ多次数の作用である。 -/
theorem stableMultiCoreFamilyCylinder_app (r : ℕ) {A C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}} {P : SSet.{u}}
    (H : P ⟶ (A ⟶[SSet.{u}] C)) (n : SimplexCategoryᵒᵖ) :
    (stableMultiCoreFamilyCylinder r H).app n =
      uncurry (H ≫ ((stableMultiSCoreEnrichedDiagram r).obj (fun _ => n)).map A C) := by
  change uncurry ((H ≫ (stableMultiSCoreObjectEnrichedFunctor r).map A C) ≫
    simplicialSSetDiagramProjection _ _ n) = _
  rw [Category.assoc, stableMultiSCoreObjectEnrichedFunctor_projection]

/-- 同じ全反復 core 円柱の対角は、元の全豊穣反復実現族の評価そのもの。 -/
theorem stableMultiCoreFamilyCylinder_diagonal (r : ℕ) {A C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}}
    {P : SSet.{u}} (H : P ⟶ (A ⟶[SSet.{u}] C)) :
    simplicialCylinderDiagonal _ _ P (stableMultiCoreFamilyCylinder r H) =
      uncurry (H ≫ (stableMultiRealizationEnrichedFunctor r).map A C) := by
  exact (diagramFamilyCylinder_diagonal _ _ P
    (H ≫ (stableMultiSCoreObjectEnrichedFunctor r).map A C)).trans
      (congrArg (uncurry (C := SSet.{u})) (Category.assoc H
        ((stableMultiSCoreObjectEnrichedFunctor r).map A C)
          (simplicialSSetDiagramDiagonalEnrichedFunctor.map _ _)))

end SerrePositivity.KST.Fibration
