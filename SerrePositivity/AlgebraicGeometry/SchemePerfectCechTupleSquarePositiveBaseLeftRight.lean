module

public import SerrePositivity.AlgebraicGeometry.SchemePerfectCechTupleSquareBaseLeftRight
public import SerrePositivity.AlgebraicGeometry.CechConstantPositiveDoubleExact

/-!
概要：実際のF8の左右の図式を、同じ正次数の基底列へ射影する。
方針：実際の自然変換を同じ交代余面複体と正次数の商へ渡す。
規約：同じ第0項のbaseSquareの左右を目標にする。
使われ方：元の左右の短完全列から基底列への射。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicTopology
universe u
variable {R S : Type u} [CommRing R] [CommRing S] {X Y : Scheme.{u}}
variable (f : X ⟶ Spec (CommRingCat.of S)) (g : Y ⟶ Spec (CommRingCat.of R))
variable (F : Arrow.mk f ⟶ Arrow.mk g) (q : R →+* S)
variable (hq : F.right = Spec.map (CommRingCat.ofHom q))
variable {ι : Type} [Fintype ι] [DecidableEq ι] (U : ι → Y.Opens)
variable (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0) (hS : (p : S) = 0)

set_option backward.isDefEq.respectTransparency false in
/-- 元のY側の二重複体から同じ正次数の基底列への射影。 -/
def schemePerfectCechTupleSquarePositiveBaseLeftProjection :
    (alternatingCofaceMapComplex (CochainComplex (ModuleCat.{u} ℤ) ℕ)).obj
        (schemePerfectCechTupleSquareLeftFunctor f g F q hq U p hp hR hS) ⟶
      cechConstantPositiveDouble (schemePerfectCechTupleSquareBaseLeftComplex f g F q hq U p hp hR hS) :=
  (alternatingCofaceMapComplex (CochainComplex (ModuleCat.{u} ℤ) ℕ)).map
      (schemePerfectCechTupleSquareBaseLeftProjection f g F q hq U p hp hR hS) ≫
    cechConstantPositiveDoubleProjection
      (schemePerfectCechTupleSquareBaseLeftComplex f g F q hq U p hp hR hS)

set_option backward.isDefEq.respectTransparency false in
/-- 元の中心側の二重複体から同じ正次数の基底列への射影。 -/
def schemePerfectCechTupleSquarePositiveBaseRightProjection :
    (alternatingCofaceMapComplex (CochainComplex (ModuleCat.{u} ℤ) ℕ)).obj
        (schemePerfectCechTupleSquareRightFunctor f g F q hq U p hp hR hS) ⟶
      cechConstantPositiveDouble (schemePerfectCechTupleSquareBaseRightComplex f g F q hq U p hp hR hS) :=
  (alternatingCofaceMapComplex (CochainComplex (ModuleCat.{u} ℤ) ℕ)).map
      (schemePerfectCechTupleSquareBaseRightProjection f g F q hq U p hp hR hS) ≫
    cechConstantPositiveDoubleProjection
      (schemePerfectCechTupleSquareBaseRightComplex f g F q hq U p hp hR hS)

set_option backward.isDefEq.respectTransparency false in
/-- 同じY側の射影は全ての外次数・縦次数の成分で全射。 -/
theorem schemePerfectCechTupleSquarePositiveBaseLeftProjection_surjective (n b : ℕ) :
    Function.Surjective
      (((schemePerfectCechTupleSquarePositiveBaseLeftProjection f g F q hq U p hp hR hS).f n).f b).hom :=
  (cechConstantPositiveDoubleProjection_surjective
    (schemePerfectCechTupleSquareBaseLeftComplex f g F q hq U p hp hR hS) n b).comp
      (schemePerfectCechTupleSquareBaseLeftProjection_surjective f g F q hq U p hp hR hS
        (SimplexCategory.mk n) b)

set_option backward.isDefEq.respectTransparency false in
/-- 同じ中心側の射影は全ての外次数・縦次数の成分で全射。 -/
theorem schemePerfectCechTupleSquarePositiveBaseRightProjection_surjective (n b : ℕ) :
    Function.Surjective
      (((schemePerfectCechTupleSquarePositiveBaseRightProjection f g F q hq U p hp hR hS).f n).f b).hom :=
  (cechConstantPositiveDoubleProjection_surjective
    (schemePerfectCechTupleSquareBaseRightComplex f g F q hq U p hp hR hS) n b).comp
      (schemePerfectCechTupleSquareBaseRightProjection_surjective f g F q hq U p hp hR hS
        (SimplexCategory.mk n) b)

end SerrePositivity.AlgebraicGeometry
