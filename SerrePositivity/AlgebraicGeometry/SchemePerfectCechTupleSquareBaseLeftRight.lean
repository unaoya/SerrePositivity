module

public import SerrePositivity.AlgebraicGeometry.CechAugmentedSquareBaseLeftRightSurjective
public import SerrePositivity.AlgebraicGeometry.SchemePerfectCechTupleSquareLeftRight

/-!
概要：実際のF8の左右の図式から同じ定数基底図式への射影。
方針：元のMapレベルの基底射影に左右の射の操作を適用する。
規約：各基底図式は元の第0項の同じbaseSquareから取る。
使われ方：元の左右の短完全列と基底列の可換な比較。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
universe u
variable {R S : Type u} [CommRing R] [CommRing S] {X Y : Scheme.{u}}
variable (f : X ⟶ Spec (CommRingCat.of S)) (g : Y ⟶ Spec (CommRingCat.of R))
variable (F : Arrow.mk f ⟶ Arrow.mk g) (q : R →+* S)
variable (hq : F.right = Spec.map (CommRingCat.ofHom q))
variable {ι : Type} [Fintype ι] [DecidableEq ι] (U : ι → Y.Opens)
variable (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0) (hS : (p : S) = 0)

set_option backward.isDefEq.respectTransparency false in
private theorem schemeSquareBaseMap_comm {m n : SimplexCategory} (a : m ⟶ n) :
    (schemePerfectCechTupleSquare_map f g F q hq U p hp hR hS a).comp
        (CechAugmentedSquare.Map.baseProjection
          (schemePerfectCechTupleSquare f g F q hq U p hp hR hS n)) =
      CechAugmentedSquare.Map.baseProjection
        (schemePerfectCechTupleSquare f g F q hq U p hp hR hS m) := by
  apply CechAugmentedSquare.Map.ext_components
  · exact comp_zero
  · exact comp_zero
  · rfl
  · rfl

/-- 元の同じ第0項の基底四角形のY側の全複体。 -/
def schemePerfectCechTupleSquareBaseLeftComplex : CochainComplex (ModuleCat.{u} ℤ) ℕ :=
  (schemePerfectCechTupleSquare f g F q hq U p hp hR hS (SimplexCategory.mk 0)).baseSquare.leftSquare.totalComplex

/-- 元の同じ第0項の基底四角形の中心側の全複体。 -/
def schemePerfectCechTupleSquareBaseRightComplex : CochainComplex (ModuleCat.{u} ℤ) ℕ :=
  (schemePerfectCechTupleSquare f g F q hq U p hp hR hS (SimplexCategory.mk 0)).baseSquare.rightSquare.totalComplex

set_option backward.isDefEq.respectTransparency false in
/-- 実際のY側の図式から、同じ定数基底図式への射影。 -/
def schemePerfectCechTupleSquareBaseLeftProjection :
    schemePerfectCechTupleSquareLeftFunctor f g F q hq U p hp hR hS ⟶
      (Functor.const SimplexCategory).obj
        (schemePerfectCechTupleSquareBaseLeftComplex f g F q hq U p hp hR hS) where
  app n := ((CechAugmentedSquare.Map.baseProjection
    (schemePerfectCechTupleSquare f g F q hq U p hp hR hS n)).onLeftSquare).totalComplexMap
  naturality {m n} a := by
    let d := schemePerfectCechTupleSquare_map f g F q hq U p hp hR hS a
    let π := CechAugmentedSquare.Map.baseProjection
      (schemePerfectCechTupleSquare f g F q hq U p hp hR hS n)
    have h := (CechAugmentedSquare.Map.onLeftSquare_comp d π).symm.trans
      (congrArg CechAugmentedSquare.Map.onLeftSquare
        (schemeSquareBaseMap_comm f g F q hq U p hp hR hS a))
    exact ((CechAugmentedSquare.Map.totalComplexMap_comp d.onLeftSquare π.onLeftSquare).symm.trans
      (congrArg CechAugmentedSquare.Map.totalComplexMap h)).trans (Category.comp_id _).symm

set_option backward.isDefEq.respectTransparency false in
/-- 実際の中心側の図式から、同じ定数基底図式への射影。 -/
def schemePerfectCechTupleSquareBaseRightProjection :
    schemePerfectCechTupleSquareRightFunctor f g F q hq U p hp hR hS ⟶
      (Functor.const SimplexCategory).obj
        (schemePerfectCechTupleSquareBaseRightComplex f g F q hq U p hp hR hS) where
  app n := ((CechAugmentedSquare.Map.baseProjection
    (schemePerfectCechTupleSquare f g F q hq U p hp hR hS n)).onRightSquare).totalComplexMap
  naturality {m n} a := by
    let d := schemePerfectCechTupleSquare_map f g F q hq U p hp hR hS a
    let π := CechAugmentedSquare.Map.baseProjection
      (schemePerfectCechTupleSquare f g F q hq U p hp hR hS n)
    have h := (CechAugmentedSquare.Map.onRightSquare_comp d π).symm.trans
      (congrArg CechAugmentedSquare.Map.onRightSquare
        (schemeSquareBaseMap_comm f g F q hq U p hp hR hS a))
    exact ((CechAugmentedSquare.Map.totalComplexMap_comp d.onRightSquare π.onRightSquare).symm.trans
      (congrArg CechAugmentedSquare.Map.totalComplexMap h)).trans (Category.comp_id _).symm

set_option backward.isDefEq.respectTransparency false in
/-- 実際のY側の同じ射影の全ての成分は全射。 -/
theorem schemePerfectCechTupleSquareBaseLeftProjection_surjective (n : SimplexCategory) (k : ℕ) :
    Function.Surjective
      (((schemePerfectCechTupleSquareBaseLeftProjection f g F q hq U p hp hR hS).app n).f k).hom :=
  CechAugmentedSquare.baseProjection_onLeftSquare_totalComplexMap_surjective
    (schemePerfectCechTupleSquare f g F q hq U p hp hR hS n) k

set_option backward.isDefEq.respectTransparency false in
/-- 実際の中心側の同じ射影の全ての成分は全射。 -/
theorem schemePerfectCechTupleSquareBaseRightProjection_surjective (n : SimplexCategory) (k : ℕ) :
    Function.Surjective
      (((schemePerfectCechTupleSquareBaseRightProjection f g F q hq U p hp hR hS).app n).f k).hom :=
  CechAugmentedSquare.baseProjection_onRightSquare_totalComplexMap_surjective
    (schemePerfectCechTupleSquare f g F q hq U p hp hR hS n) k

end SerrePositivity.AlgebraicGeometry
