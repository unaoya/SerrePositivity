module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ResolvedCoefficientHomSpan
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.PinchedComplexModelComparison

/-! 元の係数の空間模型を、元の代表加群からの実 Hom 空間へ同型で移す。 -/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded
variable {R : Type u} [CommRing R]

def dgGluingComplexPinchedMapIso {K L : Complex R} (e : K ≅ L) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSpace.{u, v} K ≅ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSpace.{u, v} L where
  hom := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap e.hom
  inv := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap e.inv
  hom_inv_id := by rw [← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap_comp, e.hom_inv_id, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap_id]
  inv_hom_id := by rw [← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap_comp, e.inv_hom_id, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap_id]

def dgGluingCoefficientYonedaSpaceIso (R : Type u) [CommRing R]
    (C : Type v) [DGCategory R C] [Small.{u} C] (c : C) (N : RightModule R C) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSpace.{u, max (u + 1) v} (N.obj (Opposite.op c)) ≅
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom R (RightModule R C) (representable R c) N :=
  dgGluingComplexPinchedMapIso (dgYonedaIso R c N).symm ≪≫
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedComplexModelIso (representable R c) N).symm

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
