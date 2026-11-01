module
public import SerrePositivity.DifferentialGraded.Tensor.Enriched
public import Mathlib.Data.ZMod.Basic

/-! # 上に有界flatと任意の非有界相手のK-flat検査 -/
@[expose] public section
noncomputable section
universe u
open CategoryTheory Limits HomologicalComplex
open SerrePositivity SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

example (K L : Complex A) (b : ℤ)
    (hb : ∀ i, b < i → IsZero (K.X i)) (hflat : ∀ i, Module.Flat A (K.X i))
    (hL : L.Acyclic) : (cochainTensor K L).Acyclic :=
  complexKFlat_of_flat_boundedAbove A K b hb hflat L hL

example (K : Complex A) (b : ℤ)
    (hb : ∀ i, b < i → IsZero (K.X i)) (hflat : ∀ i, Module.Flat A (K.X i))
    {L L' : Complex A} (f : L ⟶ L') [QuasiIso f] :
    QuasiIso (cochainTensorMap (𝟙 K) f) :=
  complexTensor_quasiIso_right_of_flat_boundedAbove A K b hb hflat f

example (K : Complex (ZMod 2)) (b : ℤ)
    (hb : ∀ i, b < i → IsZero (K.X i)) (hflat : ∀ i, Module.Flat (ZMod 2) (K.X i)) :
    complexKFlat (ZMod 2) K :=
  complexKFlat_of_flat_boundedAbove (ZMod 2) K b hb hflat

example (K : Complex A) : colimit (lowerTruncationSequence A K) ≅ K :=
  lowerTruncationColimitIso A K

#print axioms lowerTruncationMapComponent
#print axioms lowerTruncationMapComponent_inclusion
#print axioms lowerTruncationMap
#print axioms lowerTruncationMap_inclusion
#print axioms lowerTruncationMap_id
#print axioms lowerTruncationMap_comp
#print axioms lowerTruncationSequence
#print axioms lowerTruncationCocone
#print axioms lowerTruncationCoconeIsColimit
#print axioms lowerTruncationColimitIso
#print axioms complexKFlat_of_flat_boundedAbove
#print axioms complexTensor_quasiIso_right_of_flat_boundedAbove
#print axioms complexTensor_quasiIso_left_of_flat_boundedAbove
