module
public import SerrePositivity.InfinityCategories.F1B.PinchedFamilyComposition
public import SerrePositivity.InfinityCategories.Derived.DGPinchedCompositionHomotopy

/-!
概要：実 dg Hom の AW 合成族をパラメータ関手圏の実合成へ接続する。
方針：全底付き slice prism を pinched Hom の族の合成判定へ渡す。
規約：前三角性・有限性を仮定しない。使われ方：実屋根の四三角形族の評価。
-/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory DifferentialGraded DGNerve SSet
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]
/-- 実 dg Hom の任意族が表す、定値関手間の h Fun の射。 -/
noncomputable def dgPinchedFamilyHom {K : SSet.{max u v}} {x y : D}
    (f : K ⟶ DGNerve.pinchedHom A D x y) :=
  intervalFamilyHom (f ≫ pinchedHomToIntervalMappingSpace (X := dgNerve A D)
    (Simplex.vertex x) (Simplex.vertex y))
/-- 指定三族の slice 比較と全射影から、同じ h Fun の三射の合成を得る。 -/
lemma dgPinchedFamilyHom_comp_of_sliceHomotopy {K : SSet.{max u v}} {x y z : D}
    (f : K ⟶ DGNerve.pinchedHom A D x y) (g : K ⟶ DGNerve.pinchedHom A D y z)
    (c : K ⟶ DGNerve.pinchedHom A D x z)
    (H : SSet.Homotopy (c ≫ dgPinchedHomSlice A D x z) (g ≫ dgPinchedHomSlice A D y z))
    (hp : H.h ≫ sliceOverProjection _ =
      (intervalFamilyHomotopy (f ≫ pinchedHomToIntervalMappingSpace (X := dgNerve A D)
        (Simplex.vertex x) (Simplex.vertex y))).h) :
    dgPinchedFamilyHom A D f ≫ dgPinchedFamilyHom A D g = dgPinchedFamilyHom A D c := by
  exact pinchedSliceHomotopyFamily_comp f g c H hp
/-- 全次元の実 AW 合成は、任意パラメータ関手圏の合成を表す。 -/
lemma dgPinchedFamilyHom_comp {K : SSet.{max u v}} {x y z : D}
    (f : K ⟶ DGNerve.pinchedHom A D x y) (g : K ⟶ DGNerve.pinchedHom A D y z) :
    dgPinchedFamilyHom A D f ≫ dgPinchedFamilyHom A D g =
      dgPinchedFamilyHom A D (pinchedHomCompositionFamily f g) := by
  exact dgPinchedFamilyHom_comp_of_sliceHomotopy A D f g _
    (dgPinchedCompositionFamilyHomotopy A D f g)
    (dgPinchedCompositionFamilyHomotopy_over A D f g)
end SerrePositivity.InfinityCategories
