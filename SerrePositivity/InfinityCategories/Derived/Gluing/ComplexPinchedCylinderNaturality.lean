module
public import SerrePositivity.InfinityCategories.Derived.Gluing.ComplexPinchedCylinderPrism
public import SerrePositivity.InfinityCategories.Derived.Gluing.CochainCylinderMap
public import SerrePositivity.InfinityCategories.Derived.Gluing.RelativePrismHomotopy

/-! 主円柱 prism の鎖写像に沿う自然性を、二端と全基底を固定する実二次元族で実現する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory CartesianMonoidalCategory DifferentialGraded
open scoped Simplicial
variable {R : Type u} [CommRing R] {K L : Complex R} (a : K ⟶ L)

def dgGluingComplexPinchedCylinderMapPrism :=
  dgGluingComplexPinchedCylinderPrism.{u, v} K ≫
    complexPinchedMap.{u, v} (dgGluingCochainCylinderMap a)

def dgGluingComplexPinchedCylinderPrecompPrism :=
  ((Δ[1] : SSet.{max u v}) ◁ complexPinchedMap.{u, v} a) ≫
    dgGluingComplexPinchedCylinderPrism.{u, v} L

lemma dgGluingComplexPinchedCylinderPrisms_zero :
    prismEndpoint 0 _ ≫ dgGluingComplexPinchedCylinderMapPrism.{u, v} a =
      prismEndpoint 0 _ ≫ dgGluingComplexPinchedCylinderPrecompPrism.{u, v} a := by
  rw [dgGluingComplexPinchedCylinderMapPrism, ← Category.assoc,
    dgGluingComplexPinchedCylinderPrism_zero, ← complexPinchedMap_comp,
    dgGluingCochainCylinderMap_zero, complexPinchedMap_comp]
  rw [dgGluingComplexPinchedCylinderPrecompPrism, ← Category.assoc,
    prismEndpoint_naturality, Category.assoc, dgGluingComplexPinchedCylinderPrism_zero]

lemma dgGluingComplexPinchedCylinderPrisms_one :
    prismEndpoint 1 _ ≫ dgGluingComplexPinchedCylinderMapPrism.{u, v} a =
      prismEndpoint 1 _ ≫ dgGluingComplexPinchedCylinderPrecompPrism.{u, v} a := by
  rw [dgGluingComplexPinchedCylinderMapPrism, ← Category.assoc,
    dgGluingComplexPinchedCylinderPrism_one, ← complexPinchedMap_comp,
    dgGluingCochainCylinderMap_one, complexPinchedMap_comp]
  rw [dgGluingComplexPinchedCylinderPrecompPrism, ← Category.assoc,
    prismEndpoint_naturality, Category.assoc, dgGluingComplexPinchedCylinderPrism_one]

lemma dgGluingComplexPinchedCylinderPrisms_over :
    dgGluingComplexPinchedCylinderMapPrism.{u, v} a ≫
        complexPinchedMap.{u, v} (dgGluingCochainCylinderProjection L) =
      dgGluingComplexPinchedCylinderPrecompPrism.{u, v} a ≫
        complexPinchedMap.{u, v} (dgGluingCochainCylinderProjection L) := by
  rw [dgGluingComplexPinchedCylinderMapPrism, Category.assoc, ← complexPinchedMap_comp,
    dgGluingCochainCylinderMap_projection, complexPinchedMap_comp, ← Category.assoc,
    dgGluingComplexPinchedCylinderPrism_over]
  rw [dgGluingComplexPinchedCylinderPrecompPrism, Category.assoc,
    dgGluingComplexPinchedCylinderPrism_over, whiskerLeft_snd]

lemma dgGluingComplexPinchedCylinderNaturality_exists :
    ∃ H : SSet.Homotopy (dgGluingComplexPinchedCylinderMapPrism.{u, v} a)
        (dgGluingComplexPinchedCylinderPrecompPrism.{u, v} a),
      (((SSet.boundary 1).ι ▷ complexPinchedSpace.{u, v} K) ▷
          (Δ[1] : SSet.{max u v})) ≫ H.h =
        fst ((SSet.boundary 1 : SSet.{max u v}) ⊗ complexPinchedSpace.{u, v} K)
          (Δ[1] : SSet.{max u v}) ≫
          ((SSet.boundary 1).ι ▷ complexPinchedSpace.{u, v} K) ≫
          dgGluingComplexPinchedCylinderPrecompPrism.{u, v} a ∧
      H.h ≫ complexPinchedMap.{u, v} (dgGluingCochainCylinderProjection L) =
        fst ((Δ[1] : SSet.{max u v}) ⊗ complexPinchedSpace.{u, v} K)
          (Δ[1] : SSet.{max u v}) ≫ dgGluingComplexPinchedCylinderPrecompPrism.{u, v} a ≫
          complexPinchedMap.{u, v} (dgGluingCochainCylinderProjection L) := by
  let : QuasiIso (dgGluingCochainCylinderProjection L) :=
    dgGluingCochainCylinderProjection_quasiIso L
  let : TrivialKanFibration (complexPinchedMap.{u, v} (dgGluingCochainCylinderProjection L)) :=
    complexPinchedMap_trivialKanFibration _ (dgGluingCochainCylinderProjection_surjective L)
  exact dgGluingRelativePrismHomotopy_exists
    (complexPinchedMap.{u, v} (dgGluingCochainCylinderProjection L)) _ _
    (dgGluingComplexPinchedCylinderPrisms_zero a)
    (dgGluingComplexPinchedCylinderPrisms_one a)
    (dgGluingComplexPinchedCylinderPrisms_over a)

end SerrePositivity.InfinityCategories
