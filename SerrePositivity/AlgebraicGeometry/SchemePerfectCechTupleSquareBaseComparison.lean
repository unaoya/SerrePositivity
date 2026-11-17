module

public import SerrePositivity.AlgebraicGeometry.SchemePerfectCechTupleSquarePositiveBaseLeftRight
public import SerrePositivity.AlgebraicGeometry.SchemePerfectCechTupleSquareReducedDouble

/-!
概要：実際のF8の左右の短完全列を、同じ基底列へ比較する。
方針：中央と左右の同じ射影を、元の自然性で一つの短複体の射にする。
規約：元の第0項の同じbaseSquareと実際の各項・射を保持する。
使われ方：同じ三つの射影の核の短完全列。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
universe u
local notation "up" => ComplexShape.up ℕ
variable {R S : Type u} [CommRing R] [CommRing S] {X Y : Scheme.{u}}
variable (f : X ⟶ Spec (CommRingCat.of S)) (g : Y ⟶ Spec (CommRingCat.of R))
variable (F : Arrow.mk f ⟶ Arrow.mk g) (q : R →+* S)
variable (hq : F.right = Spec.map (CommRingCat.ofHom q))
variable {ι : Type} [Fintype ι] [DecidableEq ι] (U : ι → Y.Opens)
variable (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0) (hS : (p : S) = 0)

/-- 同じ第0項の基底四角形の左右の列を、同じ正次数の商へ渡す。 -/
def schemePerfectCechTupleSquareBaseLeftRightShortComplex :
    ShortComplex (HomologicalComplex₂ (ModuleCat.{u} ℤ) up up) :=
  (CechAugmentedSquare.leftRightShortComplex
    (schemePerfectCechTupleSquare f g F q hq U p hp hR hS (SimplexCategory.mk 0)).baseSquare).map
      cechConstantPositiveDoubleFunctor

/-- 同じ正次数の基底列は短完全。 -/
theorem schemePerfectCechTupleSquareBaseLeftRight_shortExact :
    (schemePerfectCechTupleSquareBaseLeftRightShortComplex f g F q hq U p hp hR hS).ShortExact :=
  cechConstantPositiveDouble_shortExact _ (CechAugmentedSquare.leftRight_shortExact _)

set_option backward.isDefEq.respectTransparency false in
/-- 実際のF8の同じ短完全列から、同じ正次数の基底列への射。 -/
def schemePerfectCechTupleSquareBaseComparison :
    schemePerfectCechTupleSquarePositiveLeftRightShortComplex f g F q hq U p hp hR hS ⟶
      schemePerfectCechTupleSquareBaseLeftRightShortComplex f g F q hq U p hp hR hS where
  τ₁ := schemePerfectCechTupleSquarePositiveBaseRightProjection f g F q hq U p hp hR hS
  τ₂ := schemePerfectCechTupleSquarePositiveBaseProjection f g F q hq U p hp hR hS
  τ₃ := schemePerfectCechTupleSquarePositiveBaseLeftProjection f g F q hq U p hp hR hS
  comm₁₂ := by
    apply HomologicalComplex.Hom.ext
    funext n
    cases n with
    | zero =>
      have hz : IsZero (HomologicalComplex.zero : CochainComplex (ModuleCat.{u} ℤ) ℕ) :=
        HomologicalComplex.isZero_zero
      exact hz.eq_of_tgt _ _
    | succ n =>
      let s := schemePerfectCechTupleSquare f g F q hq U p hp hR hS (SimplexCategory.mk (n + 1))
      let m := CechAugmentedSquare.Map.baseProjection s
      have h := (CechAugmentedSquare.Map.totalComplexMap_comp m.onRightSquare
        (CechAugmentedSquare.Map.rightInclusion s.baseSquare)).symm.trans
          ((congrArg CechAugmentedSquare.Map.totalComplexMap
            (CechAugmentedSquare.rightInclusion_naturality m)).trans
              (CechAugmentedSquare.Map.totalComplexMap_comp
                (CechAugmentedSquare.Map.rightInclusion s) m))
      exact h
  comm₂₃ := by
    apply HomologicalComplex.Hom.ext
    funext n
    cases n with
    | zero =>
      have hz : IsZero (HomologicalComplex.zero : CochainComplex (ModuleCat.{u} ℤ) ℕ) :=
        HomologicalComplex.isZero_zero
      exact hz.eq_of_tgt _ _
    | succ n =>
      let s := schemePerfectCechTupleSquare f g F q hq U p hp hR hS (SimplexCategory.mk (n + 1))
      let m := CechAugmentedSquare.Map.baseProjection s
      have h := (CechAugmentedSquare.Map.totalComplexMap_comp m
        (CechAugmentedSquare.Map.leftProjection s.baseSquare)).symm.trans
          ((congrArg CechAugmentedSquare.Map.totalComplexMap
            (CechAugmentedSquare.leftProjection_naturality m)).trans
              (CechAugmentedSquare.Map.totalComplexMap_comp
                (CechAugmentedSquare.Map.leftProjection s) m.onLeftSquare))
      exact h

end SerrePositivity.AlgebraicGeometry
