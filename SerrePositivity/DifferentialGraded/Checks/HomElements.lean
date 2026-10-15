module
public import SerrePositivity.DifferentialGraded.Module.HomElements

/-! # U10b4a：主Hom endの全次数要素の受入検査 -/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.DifferentialGraded.Checks
open CategoryTheory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

example {M N : RightModule A D} (q : ℤ)
    (h : ∀ x : Dᵒᵖ, Homogeneous (M.obj x) (N.obj x) q)
    (hn : ∀ (x y : Dᵒᵖ) (p : ℤ) (f : GradedHom A x y p),
      ((M.map x y).f p f).comp (h y) (by omega : p + q = q + p) =
        (q * p).negOnePow • ((h x).comp ((N.map x y).f p f) rfl)) (x : D) :
    (moduleHomπ A D M N x).f q (moduleHomElementMk A D q h hn) = h (op x) :=
  moduleHomElementMk_π A D q h hn x

example {M N : RightModule A D} (q : ℤ) (z : (moduleHom A D M N).X q) :
    moduleHomElementMk A D q (fun x => (moduleHomπ A D M N x.unop).f q z)
      (moduleHomElement_naturality A D q z) = z := moduleHomElementMk_components A D q z

example {M N : RightModule A D} (q r : ℤ) (z : (moduleHom A D M N).X q) (x : D) :
    (moduleHomπ A D M N x).f r ((moduleHom A D M N).d q r z) =
      δ q r ((moduleHomπ A D M N x).f q z) := moduleHomElement_d_π A D q r z x

example {M N : RightModule A D} {q : ℤ} {z w : (moduleHom A D M N).X q}
    (h : ∀ x : D, (moduleHomπ A D M N x).f q z = (moduleHomπ A D M N x).f q w) :
    z = w := moduleHomElement_ext A D h
end SerrePositivity.DifferentialGraded.Checks

open SerrePositivity.DifferentialGraded
#print axioms complexDiskHomEquiv_symm_generator
#print axioms moduleParamRelationLeft_apply
#print axioms moduleParamRelationRight_apply
#print axioms moduleHomDiskFamily
#print axioms moduleHomDiskFamily_naturality
#print axioms moduleHomElementFamilyMap
#print axioms moduleHomElementFamilyMap_condition
#print axioms moduleHomElementMk
#print axioms moduleHomElementMk_π
#print axioms moduleHomElement_ext
#print axioms moduleHomElement_naturality
#print axioms moduleHomElementMk_components
#print axioms moduleHomElement_d_π
