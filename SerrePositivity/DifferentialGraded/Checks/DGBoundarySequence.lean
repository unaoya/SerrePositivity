module
public import SerrePositivity.DifferentialGraded.Resolution.BoundarySequence
public import Mathlib.Data.ZMod.Basic

/-! # 境界cellの可換squareと逐次列の準同型判定の監査 -/
@[expose] public section
noncomputable section
universe u v w
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (S : Type v) (D : Type w)
  [DGCategory A S] [DGCategory A D] [Small.{u} S]

-- targetの対象集合のsmallnessはcell添字に不要。
example (F : DGFunctor A S D) : Small.{u} (DGCategoryBoundaryCells.Index A S D F) :=
  inferInstance

example (F : DGFunctor A S D) (x y : S) (c : ComplexBoundaryCell A (F.map x y)) :
    c.attachingMap A ≫ F.map x y = complexSphereToDisk A c.degree ≫ c.targetDiskMap A :=
  c.augmentation_square A

example (F : DGFunctor A S D) (x y : S)
    (h : ∀ c : ComplexBoundaryCell A (F.map x y), c.HasFilling A) :
    QuasiIso (F.map x y) := ComplexBoundaryCell.quasiIso_of_filling A h

example (D : Type v) [DGCategory (ZMod 2) D] [Small.{0} D] :
    Small.{0} (DGCategoryBoundaryCells.Index (ZMod 2)
      (DGCategoryCycleCover.Source (ZMod 2) D) D (DGCategoryCycleCover.augmentation (ZMod 2) D)) :=
  inferInstance

#print axioms SerrePositivity.DifferentialGraded.ComplexBoundaryCell
#print axioms SerrePositivity.DifferentialGraded.ComplexBoundaryCell.attachingMap
#print axioms SerrePositivity.DifferentialGraded.ComplexBoundaryCell.targetDiskMap
#print axioms SerrePositivity.DifferentialGraded.ComplexBoundaryCell.targetDiskMap_generator
#print axioms SerrePositivity.DifferentialGraded.ComplexBoundaryCell.augmentation_square
#print axioms SerrePositivity.DifferentialGraded.ComplexBoundaryCell.HasFilling
#print axioms SerrePositivity.DifferentialGraded.ComplexBoundaryCell.quasiIso_of_filling
#print axioms SerrePositivity.DifferentialGraded.DGCategoryBoundaryCells.Index
#print axioms SerrePositivity.DifferentialGraded.DGCategoryBoundaryCells.indexSmall
#print axioms SerrePositivity.DifferentialGraded.ComplexBoundaryCell.sequential_filling
#print axioms SerrePositivity.DifferentialGraded.ComplexBoundaryCell.sequential_quasiIso
