module
public import SerrePositivity.DifferentialGraded.Resolution.Initial
public import Mathlib.Data.ZMod.Basic

/-! # 初期dg圏増大の宇宙・K-flat性・全cycle持ち上げの監査 -/
@[expose] public section
noncomputable section
universe u v
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.DGCategoryCycleCover
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

example : DGCategory A (Source A D) := inferInstance
example : Small.{u} (Source A D) := inferInstance
example : localHomKFlat A (Source A D) := source_homKFlat A D
example : DGFunctor A (Source A D) D := augmentation A D
example : (augmentation A D).onHomotopy.EssSurj := augmentation_essSurj A D

-- 元のHomにK-flat性を課さず、任意整数次数のcycleを厳密に持ち上げる。
example (x y : D) (n : ℤ) (z : complexCycles A (homObject A D x y) n) :
    ∃ t : complexCycles A (homObject A (Source A D) x y) n,
      ((augmentation A D).map x y).f n t.val = z.val := cycle_lift A D x y n z

example (x y : D) (n : ℤ) : Epi (homologyMap ((augmentation A D).map x y) n) :=
  homologyMap_epi A D x y n

example (D : Type v) [DGCategory (ZMod 2) D] [Small.{0} D] :
    localHomKFlat (ZMod 2) (Source (ZMod 2) D) := source_homKFlat (ZMod 2) D

#print axioms SerrePositivity.DifferentialGraded.complexSphereCycle_comp
#print axioms SerrePositivity.DifferentialGraded.ComplexCycleIndex
#print axioms SerrePositivity.DifferentialGraded.complexCycleCover
#print axioms SerrePositivity.DifferentialGraded.complexCycleCoverπ
#print axioms SerrePositivity.DifferentialGraded.complexCycleCoverι_π
#print axioms SerrePositivity.DifferentialGraded.complexCycleCover_kFlat
#print axioms SerrePositivity.DifferentialGraded.complexCycleCoverLift
#print axioms SerrePositivity.DifferentialGraded.complexCycleCoverLift_π
#print axioms SerrePositivity.DifferentialGraded.complexCycleCover_cycle_lift
#print axioms SerrePositivity.DifferentialGraded.complexCyclesMap_epi_of_cycle_lift
#print axioms SerrePositivity.DifferentialGraded.complexHomologyMap_epi_of_cycle_lift
#print axioms SerrePositivity.DifferentialGraded.complexCycleCover_homology_epi
#print axioms SerrePositivity.DifferentialGraded.DGCategoryCycleCover.edges
#print axioms SerrePositivity.DifferentialGraded.DGCategoryCycleCover.Source
#print axioms SerrePositivity.DifferentialGraded.DGCategoryCycleCover.augmentation
#print axioms SerrePositivity.DifferentialGraded.DGCategoryCycleCover.augmentation_obj
#print axioms SerrePositivity.DifferentialGraded.DGCategoryCycleCover.source_homKFlat
#print axioms SerrePositivity.DifferentialGraded.DGCategoryCycleCover.edge_augmentation
#print axioms SerrePositivity.DifferentialGraded.DGCategoryCycleCover.sphereLift
#print axioms SerrePositivity.DifferentialGraded.DGCategoryCycleCover.sphereLift_augmentation
#print axioms SerrePositivity.DifferentialGraded.DGCategoryCycleCover.cycle_lift
#print axioms SerrePositivity.DifferentialGraded.DGCategoryCycleCover.cyclesMap_epi
#print axioms SerrePositivity.DifferentialGraded.DGCategoryCycleCover.homologyMap_epi
#print axioms SerrePositivity.DifferentialGraded.DGCategoryCycleCover.augmentation_essSurj
