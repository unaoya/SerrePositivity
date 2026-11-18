module

public import SerrePositivity.AlgebraicGeometry.SchemePerfectCechTupleSquareFunctor
public import SerrePositivity.AlgebraicGeometry.CechAugmentedSquareBaseProjectionNaturality

/-!
概要：実際のF8余単体図式を、同じ基底と中心の定数図式へ射影する。
方針：元の各四角形の射影と、実際の単体の射の合成則を使う。
規約：同じR・S・qと元のF8の全ての射を保持する。
使われ方：余分な定数基底列を除く全複体の比較。
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

/-- 同じ基底・中心・商写像だけを残す、元の四角形の全複体。 -/
def schemePerfectCechTupleSquareBaseComplex : CochainComplex (ModuleCat.{u} ℤ) ℕ :=
  (schemePerfectCechTupleSquare f g F q hq U p hp hR hS (SimplexCategory.mk 0)).baseSquare.totalComplex

set_option backward.isDefEq.respectTransparency false in
/-- 各nerve次数の元の全複体から同じ基底全複体への射影。 -/
def schemePerfectCechTupleSquareBaseProjectionComponent (n : SimplexCategory) :
    (schemePerfectCechTupleSquareFunctor f g F q hq U p hp hR hS).obj n ⟶
      schemePerfectCechTupleSquareBaseComplex f g F q hq U p hp hR hS :=
  (CechAugmentedSquare.Map.baseProjection
    (schemePerfectCechTupleSquare f g F q hq U p hp hR hS n)).totalComplexMap

set_option backward.isDefEq.respectTransparency false in
/-- 実際の単体の射の後に射影すると、元の射影と一致する。 -/
theorem schemePerfectCechTupleSquareBaseProjection_naturality {m n : SimplexCategory}
    (a : m ⟶ n) :
    (schemePerfectCechTupleSquareFunctor f g F q hq U p hp hR hS).map a ≫
        schemePerfectCechTupleSquareBaseProjectionComponent f g F q hq U p hp hR hS n =
      schemePerfectCechTupleSquareBaseProjectionComponent f g F q hq U p hp hR hS m := by
  let d := schemePerfectCechTupleSquare_map f g F q hq U p hp hR hS a
  have h : d.comp (CechAugmentedSquare.Map.baseProjection
      (schemePerfectCechTupleSquare f g F q hq U p hp hR hS n)) =
      CechAugmentedSquare.Map.baseProjection
        (schemePerfectCechTupleSquare f g F q hq U p hp hR hS m) := by
    apply CechAugmentedSquare.Map.ext_components
    · exact comp_zero
    · exact comp_zero
    · rfl
    · rfl
  exact (CechAugmentedSquare.Map.totalComplexMap_comp d _).symm.trans
    (congrArg CechAugmentedSquare.Map.totalComplexMap h)

/-- 実際の余単体図式から同じ定数基底図式への自然な射影。 -/
def schemePerfectCechTupleSquareBaseProjection :
    schemePerfectCechTupleSquareFunctor f g F q hq U p hp hR hS ⟶
      (Functor.const SimplexCategory).obj
        (schemePerfectCechTupleSquareBaseComplex f g F q hq U p hp hR hS) where
  app := schemePerfectCechTupleSquareBaseProjectionComponent f g F q hq U p hp hR hS
  naturality {m n} a := (schemePerfectCechTupleSquareBaseProjection_naturality
    f g F q hq U p hp hR hS a).trans (Category.comp_id _).symm

set_option backward.isDefEq.respectTransparency false in
/-- 実際の同じ射影の各項の全ての次数の成分は全射。 -/
theorem schemePerfectCechTupleSquareBaseProjection_surjective (n : SimplexCategory) (k : ℕ) :
    Function.Surjective
      (((schemePerfectCechTupleSquareBaseProjection f g F q hq U p hp hR hS).app n).f k).hom :=
  CechAugmentedSquare.baseProjection_totalComplexMap_surjective
    (schemePerfectCechTupleSquare f g F q hq U p hp hR hS n) k

end SerrePositivity.AlgebraicGeometry
