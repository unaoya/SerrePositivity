module

public import SerrePositivity.AlgebraicGeometry.CechAugmentedSquareLeftRightExact
public import SerrePositivity.AlgebraicGeometry.CechAugmentedSquareLeftRightNaturality
public import SerrePositivity.AlgebraicGeometry.SchemePerfectCechTupleSquareFunctor
public import Mathlib.Algebra.Homology.HomologicalBicomplex

/-!
概要：実際のF8の中心側とY側を同じ短完全列の図式にまとめる。
方針：元の四角形の包含・射影の自然性を、同じ余単体の射へ代入する。
規約：各項と全ての単体の射を保持する。
使われ方：同じ正次数の基底列を除いた核の短完全列。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicTopology
universe u
local notation "up" => ComplexShape.up ℕ
variable {R S : Type u} [CommRing R] [CommRing S] {X Y : Scheme.{u}}
variable (f : X ⟶ Spec (CommRingCat.of S)) (g : Y ⟶ Spec (CommRingCat.of R))
variable (F : Arrow.mk f ⟶ Arrow.mk g) (q : R →+* S)
variable (hq : F.right = Spec.map (CommRingCat.ofHom q))
variable {ι : Type} [Fintype ι] [DecidableEq ι] (U : ι → Y.Opens)
variable (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0) (hS : (p : S) = 0)

/-- 元のF8のY側の同じ各項と実際の単体の射。 -/
def schemePerfectCechTupleSquareLeftFunctor :
    SimplexCategory ⥤ CochainComplex (ModuleCat.{u} ℤ) ℕ where
  obj n := (schemePerfectCechTupleSquare f g F q hq U p hp hR hS n).leftSquare.totalComplex
  map a := (schemePerfectCechTupleSquare_map f g F q hq U p hp hR hS a).onLeftSquare.totalComplexMap
  map_id n := by
    rw [schemePerfectCechTupleSquare_map_id, CechAugmentedSquare.Map.onLeftSquare_id,
      CechAugmentedSquare.Map.totalComplexMap_id]
  map_comp a b := by
    rw [schemePerfectCechTupleSquare_map_comp, CechAugmentedSquare.Map.onLeftSquare_comp,
      CechAugmentedSquare.Map.totalComplexMap_comp]

/-- 元のF8の中心側の同じ各項と実際の単体の射。 -/
def schemePerfectCechTupleSquareRightFunctor :
    SimplexCategory ⥤ CochainComplex (ModuleCat.{u} ℤ) ℕ where
  obj n := (schemePerfectCechTupleSquare f g F q hq U p hp hR hS n).rightSquare.totalComplex
  map a := (schemePerfectCechTupleSquare_map f g F q hq U p hp hR hS a).onRightSquare.totalComplexMap
  map_id n := by
    rw [schemePerfectCechTupleSquare_map_id, CechAugmentedSquare.Map.onRightSquare_id,
      CechAugmentedSquare.Map.totalComplexMap_id]
  map_comp a b := by
    rw [schemePerfectCechTupleSquare_map_comp, CechAugmentedSquare.Map.onRightSquare_comp,
      CechAugmentedSquare.Map.totalComplexMap_comp]

/-- 実際のF8図式から同じY側の図式への自然な射影。 -/
def schemePerfectCechTupleSquareLeftProjection :
    schemePerfectCechTupleSquareFunctor f g F q hq U p hp hR hS ⟶
      schemePerfectCechTupleSquareLeftFunctor f g F q hq U p hp hR hS where
  app n := (CechAugmentedSquare.Map.leftProjection
    (schemePerfectCechTupleSquare f g F q hq U p hp hR hS n)).totalComplexMap
  naturality {m n} a :=
    (CechAugmentedSquare.Map.totalComplexMap_comp _ _).symm.trans
      ((congrArg CechAugmentedSquare.Map.totalComplexMap
        (CechAugmentedSquare.leftProjection_naturality
          (schemePerfectCechTupleSquare_map f g F q hq U p hp hR hS a))).trans
            (CechAugmentedSquare.Map.totalComplexMap_comp _ _))

/-- 同じ中心側の図式から実際のF8図式への自然な包含。 -/
def schemePerfectCechTupleSquareRightInclusion :
    schemePerfectCechTupleSquareRightFunctor f g F q hq U p hp hR hS ⟶
      schemePerfectCechTupleSquareFunctor f g F q hq U p hp hR hS where
  app n := (CechAugmentedSquare.Map.rightInclusion
    (schemePerfectCechTupleSquare f g F q hq U p hp hR hS n)).totalComplexMap
  naturality {m n} a :=
    (CechAugmentedSquare.Map.totalComplexMap_comp _ _).symm.trans
      ((congrArg CechAugmentedSquare.Map.totalComplexMap
        (CechAugmentedSquare.rightInclusion_naturality
          (schemePerfectCechTupleSquare_map f g F q hq U p hp hR hS a))).trans
            (CechAugmentedSquare.Map.totalComplexMap_comp _ _))

set_option backward.isDefEq.respectTransparency false in
/-- 実際のF8の同じ包含・射影を交代余面複体へ渡した短複体。 -/
def schemePerfectCechTupleSquarePositiveLeftRightShortComplex :
    ShortComplex (HomologicalComplex₂ (ModuleCat.{u} ℤ) up up) :=
  ShortComplex.mk
    ((alternatingCofaceMapComplex (CochainComplex (ModuleCat.{u} ℤ) ℕ)).map
      (schemePerfectCechTupleSquareRightInclusion f g F q hq U p hp hR hS))
    ((alternatingCofaceMapComplex (CochainComplex (ModuleCat.{u} ℤ) ℕ)).map
      (schemePerfectCechTupleSquareLeftProjection f g F q hq U p hp hR hS)) (by
        ext n b x
        have h := CechAugmentedSquare.rightInclusion_leftProjection
          (schemePerfectCechTupleSquare f g F q hq U p hp hR hS (SimplexCategory.mk n))
        exact ConcreteCategory.congr_hom (congrArg (fun f ↦ f.f b) h) x)

set_option backward.isDefEq.respectTransparency false in
/-- 実際の同じ二重複体の短複体は各外次数で短完全。 -/
theorem schemePerfectCechTupleSquarePositiveLeftRight_shortExact :
    (schemePerfectCechTupleSquarePositiveLeftRightShortComplex
      f g F q hq U p hp hR hS).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  exact CechAugmentedSquare.leftRight_shortExact
    (schemePerfectCechTupleSquare f g F q hq U p hp hR hS (SimplexCategory.mk n))

end SerrePositivity.AlgebraicGeometry
