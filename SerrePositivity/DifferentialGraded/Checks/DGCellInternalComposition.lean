module
public import SerrePositivity.DifferentialGraded.Resolution.Cells.InternalAssociativity
public import SerrePositivity.DifferentialGraded.Resolution.Cells.InternalUnits
public import Mathlib.Data.ZMod.Basic

/-! # 任意次数cell pathの内部合成・単位・結合則の監査 -/
@[expose] public section
noncomputable section
universe u v w
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.DGCellAttachment
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]
  (I : Type w) [Small.{u} I] (C : Family A D I)

example (x y : D) :
    (λ_ (C.internalHom A D I x y)).inv ≫
      C.internalIdentity A D I x ▷ C.internalHom A D I x y ≫
      C.internalComposition A D I x x y = 𝟙 _ := C.internalComposition_left_unit A D I x y

example (x y : D) :
    (ρ_ (C.internalHom A D I x y)).inv ≫
      C.internalHom A D I x y ◁ C.internalIdentity A D I y ≫
      C.internalComposition A D I x y y = 𝟙 _ := C.internalComposition_right_unit A D I x y

example (x y z t : D) :
    (C.internalComposition A D I x y z ▷ C.internalHom A D I z t) ≫
      C.internalComposition A D I x z t =
    (α_ (C.internalHom A D I x y) (C.internalHom A D I y z) (C.internalHom A D I z t)).hom ≫
      C.internalHom A D I x y ◁ C.internalComposition A D I y z t ≫
        C.internalComposition A D I x y t := C.internalComposition_assoc A D I x y z t

-- 体・有界性・元のHomのflatness・Dの対象smallnessを要求しない。
example (D : Type v) [DGCategory (ZMod 2) D] (x y : D)
    (z : complexCycles (ZMod 2) (homObject (ZMod 2) D x y) 8) :
    let C : Family (ZMod 2) D PUnit := ⟨fun _ => x, fun _ => y, fun _ => 7, fun _ => z⟩
    (ρ_ (C.internalHom (ZMod 2) D PUnit x y)).inv ≫
      C.internalHom (ZMod 2) D PUnit x y ◁ C.internalIdentity (ZMod 2) D PUnit y ≫
      C.internalComposition (ZMod 2) D PUnit x y y = 𝟙 _ := by
  exact Family.internalComposition_right_unit _ _ _ _ _ _

#print axioms SerrePositivity.DifferentialGraded.DGCellAttachment.Family.internalComposition
#print axioms
  SerrePositivity.DifferentialGraded.DGCellAttachment.Family.internalComposition_inclusion
#print axioms
  SerrePositivity.DifferentialGraded.DGCellAttachment.Family.internalComposition_original_left
#print axioms
  SerrePositivity.DifferentialGraded.DGCellAttachment.Family.internalComposition_original_original
#print axioms SerrePositivity.DifferentialGraded.DGCellAttachment.Family.appendRight
#print axioms SerrePositivity.DifferentialGraded.DGCellAttachment.Family.appendRight_inclusion
#print axioms
  SerrePositivity.DifferentialGraded.DGCellAttachment.Family.internalComposition_left_inclusion
#print axioms SerrePositivity.DifferentialGraded.DGCellAttachment.Family.internalPrepend
#print axioms SerrePositivity.DifferentialGraded.DGCellAttachment.Family.internalPrepend_inclusion
#print axioms SerrePositivity.DifferentialGraded.DGCellAttachment.Family.internalIdentity
#print axioms
  SerrePositivity.DifferentialGraded.DGCellAttachment.Family.internalComposition_left_unit
#print axioms SerrePositivity.DifferentialGraded.DGCellAttachment.Family.prefixCofanIsColimit
#print axioms SerrePositivity.DifferentialGraded.DGCellAttachment.Family.prefixPath
#print axioms SerrePositivity.DifferentialGraded.DGCellAttachment.Family.prefixPath_inclusion
#print axioms SerrePositivity.DifferentialGraded.DGCellAttachment.Family.prefixPathCochain_ext
#print axioms SerrePositivity.DifferentialGraded.DGCellAttachment.Family.appendRight_cons
#print axioms SerrePositivity.DifferentialGraded.DGCellAttachment.Family.appendRight_right_unit
#print axioms
  SerrePositivity.DifferentialGraded.DGCellAttachment.Family.internalComposition_right_unit
#print axioms SerrePositivity.DifferentialGraded.DGCellAttachment.Family.appendMap_prepend
#print axioms SerrePositivity.DifferentialGraded.DGCellAttachment.Family.appendRight_prepend
#print axioms SerrePositivity.DifferentialGraded.DGCellAttachment.Family.internalComposition_prepend
#print axioms SerrePositivity.DifferentialGraded.DGCellAttachment.Family.composition_prefix_left_ι
#print axioms SerrePositivity.DifferentialGraded.DGCellAttachment.Family.composition_prefix_middle_ι
#print axioms SerrePositivity.DifferentialGraded.DGCellAttachment.Family.composition_prefix_outer_ι
#print axioms SerrePositivity.DifferentialGraded.DGCellAttachment.Family.composition_prefix_restrict
#print axioms
  SerrePositivity.DifferentialGraded.DGCellAttachment.Family.internalComposition_prefixPath
#print axioms SerrePositivity.DifferentialGraded.DGCellAttachment.Family.appendRight_assoc
#print axioms SerrePositivity.DifferentialGraded.DGCellAttachment.Family.internalComposition_assoc
