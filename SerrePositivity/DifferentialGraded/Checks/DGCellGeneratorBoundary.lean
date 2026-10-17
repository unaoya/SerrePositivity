module
public import SerrePositivity.DifferentialGraded.Resolution.Cells.PathEvaluation
public import SerrePositivity.DifferentialGraded.Resolution.Cells.GeneratorDisk
public import Mathlib.Data.ZMod.Basic

/-! # cell生成元の境界・指定原始元・有限path評価の監査 -/
@[expose] public section
noncomputable section
universe u v w z
open CategoryTheory HomologicalComplex CochainComplex HomComplex
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.DGCellAttachment
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]
  (I : Type w) [Small.{u} I] (C : Family A D I)

example (i : I) :
    (C.attachedHom A D I (C.source i) (C.target i)).d (C.degree i) (C.degree i + 1)
      (C.generatorElement A D I i) =
    (C.originalHomInclusion A D I (C.source i) (C.target i)).f (C.degree i + 1)
      (C.boundary i).val := C.differential_generatorElement A D I i

example (E : Type z) [DGCategory A E] (F : DGFunctor A D E) :
    Family.PrimitiveData A D (DGCategoryBoundaryCells.Index A D E F)
      (boundaryFamily A D E F) E F := DGCategoryBoundaryCells.primitiveData A D E F

omit [Small.{u} I] in
example (E : Type z) [DGCategory A E] (F : DGFunctor A D E)
    (P : Family.PrimitiveData A D I C E F) (w : List I) (x y : D) :
    Cochain (C.term A D I w x y) (homObject A E (F.obj x) (F.obj y)) 0 :=
  P.pathEvaluation w x y

example (i : I) :
    complexSphereToDisk A (C.degree i) ≫ C.generatorDisk A D I i =
    complexSphereMap A (C.degree i + 1) (C.boundary i) ≫
      C.originalHomInclusion A D I (C.source i) (C.target i) :=
  C.generatorDisk_boundary A D I i

example (D : Type v) [DGCategory (ZMod 2) D] (I : Type w) [Small.{0} I]
    (C : Family (ZMod 2) D I) (i : I) :
    (C.attachedHom (ZMod 2) D I (C.source i) (C.target i)).d (C.degree i) (C.degree i + 1)
      (C.generatorElement (ZMod 2) D I i) =
    (C.originalHomInclusion (ZMod 2) D I (C.source i) (C.target i)).f (C.degree i + 1)
      (C.boundary i).val := C.differential_generatorElement (ZMod 2) D I i

#print axioms SerrePositivity.DifferentialGraded.DGCellAttachment.Family.generatorTerm_apply
#print axioms SerrePositivity.DifferentialGraded.DGCellAttachment.Family.replaceFirst_generatorTerm
#print axioms SerrePositivity.DifferentialGraded.DGCellAttachment.Family.generatorElement
#print axioms SerrePositivity.DifferentialGraded.DGCellAttachment.Family.replaceRow_singleton
#print axioms
  SerrePositivity.DifferentialGraded.DGCellAttachment.Family.replacement_generatorElement
#print axioms SerrePositivity.DifferentialGraded.DGCellAttachment.Family.internal_d_generatorElement
#print axioms
  SerrePositivity.DifferentialGraded.DGCellAttachment.Family.differential_generatorElement
#print axioms SerrePositivity.DifferentialGraded.DGCellAttachment.Family.PrimitiveData
#print axioms SerrePositivity.DifferentialGraded.DGCellAttachment.Family.PrimitiveData.cochain
#print axioms
  SerrePositivity.DifferentialGraded.DGCellAttachment.Family.PrimitiveData.cochain_generator
#print axioms
  SerrePositivity.DifferentialGraded.DGCellAttachment.Family.PrimitiveData.cochain_differential
#print axioms
  SerrePositivity.DifferentialGraded.DGCellAttachment.Family.PrimitiveData.pathEvaluation
#print axioms
  SerrePositivity.DifferentialGraded.DGCellAttachment.Family.PrimitiveData.pathEvaluation_nil
#print axioms
  DGCellAttachment.Family.PrimitiveData.pathEvaluation_cons_generator
#print axioms
  DGCellAttachment.Family.PrimitiveData.pathEvaluation_generatorTerm
#print axioms SerrePositivity.DifferentialGraded.DGCategoryBoundaryCells.primitiveData
#print axioms SerrePositivity.DifferentialGraded.DGCellAttachment.Family.forward_units_of_sum
#print axioms SerrePositivity.DifferentialGraded.DGCellAttachment.Family.generatorDisk
#print axioms SerrePositivity.DifferentialGraded.DGCellAttachment.Family.generatorDisk_generator
#print axioms SerrePositivity.DifferentialGraded.DGCellAttachment.Family.generatorDisk_boundary
