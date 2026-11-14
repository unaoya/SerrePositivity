module
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.PinchedFamilyComposition
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.PinchedModels.DGPinchedCompositionHomotopy

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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory MonoidalCategory DifferentialGraded SSet
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D]
/-- 実 dg Hom の任意族が表す、定値関手間の h Fun の射。 -/
noncomputable def dgPinchedFamilyHom {K : SSet.{max u v}} {x y : D}
    (f : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D x y) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y))
/-- 指定三族の slice 比較と全射影から、同じ h Fun の三射の合成を得る。 -/
lemma dgPinchedFamilyHom_comp_of_sliceHomotopy {K : SSet.{max u v}} {x y z : D}
    (f : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D x y) (g : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D y z)
    (c : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D x z)
    (H : SSet.Homotopy (c ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedHomSlice A D x z) (g ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedHomSlice A D y z))
    (hp : H.h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection _ =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHomotopy (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y))).h) :
    dgPinchedFamilyHom A D f ≫ dgPinchedFamilyHom A D g = dgPinchedFamilyHom A D c := by
  exact _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.pinchedSliceHomotopyFamily_comp f g c H hp
/-- 全次元の実 AW 合成は、任意パラメータ関手圏の合成を表す。 -/
lemma dgPinchedFamilyHom_comp {K : SSet.{max u v}} {x y z : D}
    (f : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D x y) (g : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D y z) :
    dgPinchedFamilyHom A D f ≫ dgPinchedFamilyHom A D g =
      dgPinchedFamilyHom A D (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomCompositionFamily f g) := by
  exact dgPinchedFamilyHom_comp_of_sliceHomotopy A D f g _
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedCompositionFamilyHomotopy A D f g)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedCompositionFamilyHomotopy_over A D f g)
end SerrePositivity.InfinityCategories.Project.DerivedCategories
