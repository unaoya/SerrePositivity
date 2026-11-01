module
public import SerrePositivity.DifferentialGraded.Tensor.Enriched
public import Mathlib.Data.ZMod.Basic

/-! # K-flat複体の閉性と任意非有界準同型の保存 -/
@[expose] public section
noncomputable section
universe u
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex
open SerrePositivity
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

example : complexKFlat A ((𝟙_ (Complex A))⟦(-1 : ℤ)⟧) :=
  complexKFlat_shift A (complexKFlat_unit A) (-1)

example {K L L' : Complex A} (h : complexKFlat A K) (f : L ⟶ L') [QuasiIso f] :
    QuasiIso (cochainTensorMap (𝟙 K) f) :=
  (complexKFlat_iff_preserves_quasiIso A K).1 h f inferInstance

example {K K' : Complex A} (f : K ⟶ K')
    (hK : complexKFlat A K) (hK' : complexKFlat A K') (L : Complex A) (hL : L.Acyclic) :
    ((mappingCone f) ⊗ L).Acyclic :=
  complexKFlat_cone A f hK hK' L hL

example : complexKFlat (ZMod 2) ((𝟙_ (Complex (ZMod 2)))⟦(1 : ℤ)⟧) :=
  complexKFlat_shift (ZMod 2) (complexKFlat_unit (ZMod 2)) 1

#print axioms complexKFlat_unit
#print axioms complexKFlat_shift
#print axioms complexKFlat_cone
#print axioms complexKFlat_tensor
#print axioms complexKFlat_of_flat_bounds
#print axioms complexKFlat_quasiIso_left
#print axioms complexKFlat_quasiIso_right
#print axioms complexKFlat_iff_preserves_quasiIso
