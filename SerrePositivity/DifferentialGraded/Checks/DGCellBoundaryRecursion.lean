module
public import SerrePositivity.DifferentialGraded.Resolution.Cells.PrefixBoundary
public import SerrePositivity.DifferentialGraded.Resolution.Cells.AppendBoundaryHead
public import SerrePositivity.DifferentialGraded.Complexes.PrefixTensorCochainPostcompose
public import Mathlib.Data.ZMod.Basic

/-! # 任意次数cellの先頭境界と全path置換の再帰式の監査 -/
@[expose] public section
noncomputable section
universe u v w
open CategoryTheory MonoidalCategory CochainComplex HomComplex
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.DGCellAttachment
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]
  (I : Type w) [Small.{u} I] (C : Family A D I)

example (b : I) (y : D) :
    Cochain (C.generator A D I b ⊗ C.internalHom A D I (C.target b) y)
      (C.internalHom A D I (C.source b) y) 1 := C.internalReplaceHead A D I b y

example (D : Type v) [DGCategory (ZMod 2) D] (I : Type w) [Small.{0} I]
    (C : Family (ZMod 2) D I) (b : I) (x y : D) :
    (Cochain.ofHom (C.prefixPath (ZMod 2) D I b x y)).comp
      (C.replacement (ZMod 2) D I x y) (zero_add 1) =
    C.internalReplaceFirst (ZMod 2) D I b x y +
    ((tensorLeftHom (homObject (ZMod 2) D x (C.source b)) _ _).f 1
      ((tensorLeftHom (C.generator (ZMod 2) D I b) _ _).f 1
        (C.replacement (ZMod 2) D I (C.target b) y))).comp
      (Cochain.ofHom (C.prefixPath (ZMod 2) D I b x y)) (add_zero 1) :=
  C.prefixPath_replacement (ZMod 2) D I b x y

#print axioms SerrePositivity.DifferentialGraded.tensorRight_cochain_chain_naturality
#print axioms SerrePositivity.DifferentialGraded.tensorCarry_cochain
#print axioms SerrePositivity.DifferentialGraded.tensorRight_action_cochain
#print axioms SerrePositivity.DifferentialGraded.prefixTensor_cochain_middle_postcompose
#print axioms SerrePositivity.DifferentialGraded.prefixTensor_cochain_right_postcompose
#print axioms SerrePositivity.DifferentialGraded.DGCellAttachment.Family.internalReplaceHead
#print axioms SerrePositivity.DifferentialGraded.DGCellAttachment.Family.internalReplaceFirst
#print axioms
  SerrePositivity.DifferentialGraded.DGCellAttachment.Family.internalReplaceHead_inclusion
#print axioms
  SerrePositivity.DifferentialGraded.DGCellAttachment.Family.internalReplaceFirst_inclusion
#print axioms SerrePositivity.DifferentialGraded.DGCellAttachment.Family.prefixTailCochain
#print axioms SerrePositivity.DifferentialGraded.DGCellAttachment.Family.replaceSummand_cons_succ
#print axioms SerrePositivity.DifferentialGraded.DGCellAttachment.Family.replaceRow_cons
#print axioms SerrePositivity.DifferentialGraded.DGCellAttachment.Family.prefixPath_replacement
#print axioms SerrePositivity.DifferentialGraded.DGCellAttachment.Family.appendRight_replaceHead
#print axioms SerrePositivity.DifferentialGraded.DGCellAttachment.Family.appendRight_replaceFirst
