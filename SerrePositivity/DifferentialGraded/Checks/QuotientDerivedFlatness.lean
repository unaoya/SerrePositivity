module
public import SerrePositivity.DifferentialGraded.Quotient.DerivedComparison.LocalFlatness

/-! # 局所 K-flat 仮定の向き・宇宙と公理監査 -/
@[expose] public section
universe u v
open SerrePositivity.DifferentialGraded.DGQuotient
variable (A : Type u) [CommRing A] (D : Type v)
  [SerrePositivity.DifferentialGraded.DGCategory A D]

example (h : allHomKFlat A D) (S : Set D) : localKFlat A D S := allHomKFlat_local A D h S
example {S T : Set D} (h : S ⊆ T) (hT : localKFlat A D T) : localKFlat A D S :=
  localKFlat_mono A D h hT

#print axioms homIntoKFlat_mono
#print axioms homOutOfKFlat_mono
#print axioms localKFlat_mono
#print axioms allHomKFlat_into
#print axioms allHomKFlat_outOf
#print axioms allHomKFlat_local
#print axioms allHomKFlat_of_flat_bounds
#print axioms allHomKFlat_of_flat_degreeZero
#print axioms allHomKFlat_of_flat_zero
