module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.MixedHomBifunctor
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.MixedBiresolutionComparison

/-! # The same raw mixed Hom on ordinary resolution pairs

Outer-frame choices are forgotten strictly. All actual inner resolution maps
and base maps are retained; no section or cofinality of forgetting is claimed.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory HomotopicalAlgebra Opposite

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryResolutionPairs
variable {C : Type u} [Category.{v} C] [ModelCategory C]

abbrev Index := (ResolutionObject C)ᵒᵖ × (ResolutionObject Cᵒᵖ)ᵒᵖ
abbrev projection : Index (C := C) ⥤ Cᵒᵖ × C :=
  ResolutionObject.projection.op.prod (ResolutionObject.projection.op ⋙ unopUnop C)

abbrev diagrams : Index (C := C) ⥤
    (SimplexCategory ⥤ C)ᵒᵖ × (SimplexCategory ⥤ Cᵒᵖ)ᵒᵖ :=
  ResolutionObject.diagrams.op.prod (ResolutionObject.diagrams (C := Cᵒᵖ)).op
abbrev raw : Index (C := C) ⥤ SSet.{v} := diagrams ⋙ MixedDiagonalHom.functor

abbrev forgetFrames : RightResolutionMapping.Index C ⥤ Index (C := C) :=
  FramedResolution.forget.op.prod (FramedResolution.forget (C := Cᵒᵖ)).op

lemma projection_eq : forgetFrames (C := C) ⋙ projection = RightResolutionMapping.projection := rfl
lemma raw_eq : forgetFrames (C := C) ⋙ raw = MixedBiresolutionComparison.functor := rfl

lemma raw_map {X Y : Index (C := C)} (f : X ⟶ Y) :
    (raw (C := C)).map f = MixedDiagonalHom.map f.1.unop.diagram f.2.unop.diagram := rfl

end SerrePositivity.HomotopyFunctionComplex.OrdinaryResolutionPairs
