module
public import SerrePositivity.KST.Fibration.StableZeroSPoint
public import SerrePositivity.KST.Fibration.SimplicialCylinderDiagonal
public import SerrePositivity.KST.Fibration.WeakStringRealizationConstants

/-! # 同じ零自己関手による全単体的円柱の、元の対角上の実収縮 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration

/-- 全 S• の同じ実円柱を、元の対角へ送る。 -/
def stableZeroSDiagonalCylinder (A : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}) :
    simplicialDiagonalFunctor.obj (simplicialSConstruction A.obj) ⊗ (Δ[1] : SSet.{u}) ⟶
      simplicialDiagonalFunctor.obj (simplicialSConstruction A.obj) :=
  simplicialCylinderDiagonal _ _ _ (stableZeroSContractionNatTrans A)

/-- 元の対角の零端は、同じ元の零自己関手の対角像そのもの。 -/
theorem stableZeroSDiagonalCylinder_zero (A : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}) :
    SSet.ι₀ ≫ stableZeroSDiagonalCylinder A =
      simplicialDiagonalFunctor.map (stableZeroSMap A) := by
  apply simplicialCylinderDiagonal_zero
  intro n
  exact uncurryIntervalFamily_zero _ _ (stableZeroSContractionFamily_zero A n.unop.len)

/-- 元の対角の終端は、元の恒等射そのもの。 -/
theorem stableZeroSDiagonalCylinder_one (A : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}) :
    SSet.ι₁ ≫ stableZeroSDiagonalCylinder A =
      𝟙 (simplicialDiagonalFunctor.obj (simplicialSConstruction A.obj)) := by
  have h := simplicialCylinderDiagonal_one (stableZeroSContractionNatTrans A)
    (𝟙 (simplicialSConstruction A.obj)) (fun n =>
      uncurryIntervalFamily_one _ _ (stableZeroSContractionFamily_one A n.unop.len))
  exact h.trans (CategoryTheory.Functor.map_id _ _)

/-- 同じ零図式点の対角像を、元の一点を始域として保持する。 -/
def stableZeroSDiagonalPoint (A : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}) :
    𝟙_ SSet.{u} ⟶ simplicialDiagonalFunctor.obj (simplicialSConstruction A.obj) :=
  (constantSSetDiagonalIso (𝟙_ SSet.{u})).inv ≫
    simplicialDiagonalFunctor.map (stableZeroSPoint A)

/-- 元の零端の対角像は、同じ一点射と同じ零図式点を厳密に通る。 -/
theorem stableZeroSDiagonalMap_factor (A : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}) :
    simplicialDiagonalFunctor.map (stableZeroSMap A) =
      toUnit _ ≫ stableZeroSDiagonalPoint A := by
  rw [stableZeroSMap_factor, CategoryTheory.Functor.map_comp]
  have ht : simplicialDiagonalFunctor.map (stableZeroSToPoint A) ≫
      (constantSSetDiagonalIso (𝟙_ SSet.{u})).hom = toUnit _ :=
    isTerminalTensorUnit.hom_ext _ _
  rw [← ht, stableZeroSDiagonalPoint, Category.assoc, Iso.hom_inv_id_assoc]

/-- 同じ全単体的円柱は、対角の元の一点への実収縮ホモトピーを与える。 -/
def stableZeroSDiagonalContraction (A : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}) :
    SSet.Homotopy (toUnit _ ≫ stableZeroSDiagonalPoint A)
      (𝟙 (simplicialDiagonalFunctor.obj (simplicialSConstruction A.obj))) where
  h := stableZeroSDiagonalCylinder A
  h₀ := (stableZeroSDiagonalCylinder_zero A).trans (stableZeroSDiagonalMap_factor A)
  h₁ := stableZeroSDiagonalCylinder_one A
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

end SerrePositivity.KST.Fibration
