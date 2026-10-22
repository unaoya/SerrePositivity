module
public import SerrePositivity.InfinityCategories.Derived.Gluing.ResolvedCoefficientHomSpan
public import SerrePositivity.InfinityCategories.Derived.PinchedComplexModelComparison

/-! 元の係数の空間模型を、元の代表加群からの実 Hom 空間へ同型で移す。 -/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded
variable {R : Type u} [CommRing R]

def dgGluingComplexPinchedMapIso {K L : Complex R} (e : K ≅ L) :
    complexPinchedSpace.{u, v} K ≅ complexPinchedSpace.{u, v} L where
  hom := complexPinchedMap e.hom
  inv := complexPinchedMap e.inv
  hom_inv_id := by rw [← complexPinchedMap_comp, e.hom_inv_id, complexPinchedMap_id]
  inv_hom_id := by rw [← complexPinchedMap_comp, e.inv_hom_id, complexPinchedMap_id]

def dgGluingCoefficientYonedaSpaceIso (R : Type u) [CommRing R]
    (C : Type v) [DGCategory R C] [Small.{u} C] (c : C) (N : RightModule R C) :
    complexPinchedSpace.{u, max (u + 1) v} (N.obj (Opposite.op c)) ≅
      DGNerve.pinchedHom R (RightModule R C) (representable R c) N :=
  dgGluingComplexPinchedMapIso (dgYonedaIso R c N).symm ≪≫
    (pinchedComplexModelIso (representable R c) N).symm

end SerrePositivity.InfinityCategories
