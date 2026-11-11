module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.AugmentationCylinderOver
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ComplexPinchedCylinderNaturality
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.CochainCylinderMap
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.RelativePrismHomotopy

/-! 明示 augmentation 円柱と鎖写像上の選択円柱を、二端・全基底固定の全二次元族で比較する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory CartesianMonoidalCategory DifferentialGraded
open scoped _root_.Simplicial
variable {R : Type u} [CommRing R] {K L : Complex R} (a : K ⟶ L)

def dgGluingAugmentationCylinderMapPrism :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingAugmentationCylinderPrism.{u, v} K ≫
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, max u v} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainCylinderMap a)

lemma dgGluingAugmentationCylinderPrisms_zero :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 _ ≫ dgGluingAugmentationCylinderMapPrism.{u, v} a =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 _ ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPinchedCylinderPrecompPrism.{u, max u v} a := by
  rw [dgGluingAugmentationCylinderMapPrism, ← Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingAugmentationCylinderPrism_zero, ← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap_comp,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainCylinderMap_zero, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap_comp]
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPinchedCylinderPrecompPrism, ← Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint_naturality, Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPinchedCylinderPrism_zero]

lemma dgGluingAugmentationCylinderPrisms_one :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 _ ≫ dgGluingAugmentationCylinderMapPrism.{u, v} a =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 _ ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPinchedCylinderPrecompPrism.{u, max u v} a := by
  rw [dgGluingAugmentationCylinderMapPrism, ← Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingAugmentationCylinderPrism_one, ← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap_comp,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainCylinderMap_one, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap_comp]
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPinchedCylinderPrecompPrism, ← Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint_naturality, Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPinchedCylinderPrism_one]

lemma dgGluingAugmentationCylinderPrisms_over :
    dgGluingAugmentationCylinderMapPrism.{u, v} a ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, max u v} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainCylinderProjection L) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPinchedCylinderPrecompPrism.{u, max u v} a ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, max u v} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainCylinderProjection L) := by
  rw [dgGluingAugmentationCylinderMapPrism, Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap_comp,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainCylinderMap_projection, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap_comp, ← Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingAugmentationCylinderPrism_over]
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPinchedCylinderPrecompPrism, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPinchedCylinderPrism_over, whiskerLeft_snd]

lemma dgGluingAugmentationCylinderNaturality_exists :
    ∃ H : SSet.Homotopy (dgGluingAugmentationCylinderMapPrism.{u, v} a)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPinchedCylinderPrecompPrism.{u, max u v} a),
      (((SSet.boundary 1).ι ▷ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSpace.{u, max u v} K) ▷
          (Δ[1] : SSet.{max u v})) ≫ H.h =
        fst ((SSet.boundary 1 : SSet.{max u v}) ⊗ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSpace.{u, max u v} K)
          (Δ[1] : SSet.{max u v}) ≫
          ((SSet.boundary 1).ι ▷ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSpace.{u, max u v} K) ≫
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPinchedCylinderPrecompPrism.{u, max u v} a ∧
      H.h ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, max u v} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainCylinderProjection L) =
        fst ((Δ[1] : SSet.{max u v}) ⊗ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSpace.{u, max u v} K)
          (Δ[1] : SSet.{max u v}) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPinchedCylinderPrecompPrism.{u, max u v} a ≫
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, max u v} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainCylinderProjection L) := by
  let : QuasiIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainCylinderProjection L) :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainCylinderProjection_quasiIso L
  let : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, max u v} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainCylinderProjection L)) :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap_trivialKanFibration _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainCylinderProjection_surjective L)
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRelativePrismHomotopy_exists
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, max u v} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainCylinderProjection L)) _ _
    (dgGluingAugmentationCylinderPrisms_zero a)
    (dgGluingAugmentationCylinderPrisms_one a)
    (dgGluingAugmentationCylinderPrisms_over a)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
