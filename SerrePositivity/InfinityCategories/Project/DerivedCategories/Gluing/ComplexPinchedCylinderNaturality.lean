module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ComplexPinchedCylinderPrism
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.CochainCylinderMap
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.RelativePrismHomotopy

/-! 主円柱 prism の鎖写像に沿う自然性を、二端と全基底を固定する実二次元族で実現する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory CartesianMonoidalCategory DifferentialGraded
open scoped _root_.Simplicial
variable {R : Type u} [CommRing R] {K L : Complex R} (a : K ⟶ L)

def dgGluingComplexPinchedCylinderMapPrism :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPinchedCylinderPrism.{u, v} K ≫
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, v} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainCylinderMap a)

def dgGluingComplexPinchedCylinderPrecompPrism :=
  ((Δ[1] : SSet.{max u v}) ◁ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, v} a) ≫
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPinchedCylinderPrism.{u, v} L

lemma dgGluingComplexPinchedCylinderPrisms_zero :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 _ ≫ dgGluingComplexPinchedCylinderMapPrism.{u, v} a =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 _ ≫ dgGluingComplexPinchedCylinderPrecompPrism.{u, v} a := by
  rw [dgGluingComplexPinchedCylinderMapPrism, ← Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPinchedCylinderPrism_zero, ← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap_comp,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainCylinderMap_zero, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap_comp]
  rw [dgGluingComplexPinchedCylinderPrecompPrism, ← Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint_naturality, Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPinchedCylinderPrism_zero]

lemma dgGluingComplexPinchedCylinderPrisms_one :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 _ ≫ dgGluingComplexPinchedCylinderMapPrism.{u, v} a =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 _ ≫ dgGluingComplexPinchedCylinderPrecompPrism.{u, v} a := by
  rw [dgGluingComplexPinchedCylinderMapPrism, ← Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPinchedCylinderPrism_one, ← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap_comp,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainCylinderMap_one, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap_comp]
  rw [dgGluingComplexPinchedCylinderPrecompPrism, ← Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint_naturality, Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPinchedCylinderPrism_one]

lemma dgGluingComplexPinchedCylinderPrisms_over :
    dgGluingComplexPinchedCylinderMapPrism.{u, v} a ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, v} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainCylinderProjection L) =
      dgGluingComplexPinchedCylinderPrecompPrism.{u, v} a ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, v} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainCylinderProjection L) := by
  rw [dgGluingComplexPinchedCylinderMapPrism, Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap_comp,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainCylinderMap_projection, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap_comp, ← Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPinchedCylinderPrism_over]
  rw [dgGluingComplexPinchedCylinderPrecompPrism, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPinchedCylinderPrism_over, whiskerLeft_snd]

lemma dgGluingComplexPinchedCylinderNaturality_exists :
    ∃ H : SSet.Homotopy (dgGluingComplexPinchedCylinderMapPrism.{u, v} a)
        (dgGluingComplexPinchedCylinderPrecompPrism.{u, v} a),
      (((SSet.boundary 1).ι ▷ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSpace.{u, v} K) ▷
          (Δ[1] : SSet.{max u v})) ≫ H.h =
        fst ((SSet.boundary 1 : SSet.{max u v}) ⊗ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSpace.{u, v} K)
          (Δ[1] : SSet.{max u v}) ≫
          ((SSet.boundary 1).ι ▷ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSpace.{u, v} K) ≫
          dgGluingComplexPinchedCylinderPrecompPrism.{u, v} a ∧
      H.h ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, v} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainCylinderProjection L) =
        fst ((Δ[1] : SSet.{max u v}) ⊗ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSpace.{u, v} K)
          (Δ[1] : SSet.{max u v}) ≫ dgGluingComplexPinchedCylinderPrecompPrism.{u, v} a ≫
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, v} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainCylinderProjection L) := by
  let : QuasiIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainCylinderProjection L) :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainCylinderProjection_quasiIso L
  let : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, v} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainCylinderProjection L)) :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap_trivialKanFibration _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainCylinderProjection_surjective L)
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRelativePrismHomotopy_exists
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, v} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainCylinderProjection L)) _ _
    (dgGluingComplexPinchedCylinderPrisms_zero a)
    (dgGluingComplexPinchedCylinderPrisms_one a)
    (dgGluingComplexPinchedCylinderPrisms_over a)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
