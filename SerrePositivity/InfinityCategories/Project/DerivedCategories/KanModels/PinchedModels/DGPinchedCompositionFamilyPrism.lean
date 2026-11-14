module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.PinchedModels.DGPinchedCompositionPrismProjection

/-! # 任意パラメータ族の実合成 prism

概要：任意の実 Hom 族から実 slice の prism を構成し、両端・射影・パラメータ制限を保つ。
方針：既存の全次数の等式を同じ写像のまま接続する。
規約：有限性・前三角性を仮定しない。使われ方：実屋根の四三角形の高次の族。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory MonoidalCategory CartesianMonoidalCategory DifferentialGraded
open SSet
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D]

/-- 任意の同時パラメータ付き実 Hom 二族からの、実 target slice の合成 prism。 -/
def dgPinchedCompositionFamilyPrism {K : SSet.{max u v}} {x y z : D}
    (f : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D x y) (g : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D y z) :
    (Δ[1] : SSet.{max u v}) ⊗ K ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex z)) :=
  (Δ[1] ◁ CartesianMonoidalCategory.lift f g) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedCompositionPrism A D x y z
/-- 族の実合成 prism の零端は、同じ全パラメータ合成族の slice 表示。 -/
lemma dgPinchedCompositionFamilyPrism_zero {K : SSet.{max u v}} {x y z : D}
    (f : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D x y) (g : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D y z) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 K ≫ dgPinchedCompositionFamilyPrism A D f g =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomCompositionFamily f g ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedHomSlice A D x z := by
  have h := congrArg (fun k => CartesianMonoidalCategory.lift f g ≫ k)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedCompositionPrism_zero A D x y z)
  dsimp only [dgPinchedCompositionFamilyPrism]
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint_naturality]
  exact h
/-- 族の実合成 prism の一端は、元の第二族の slice 表示。 -/
lemma dgPinchedCompositionFamilyPrism_one {K : SSet.{max u v}} {x y z : D}
    (f : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D x y) (g : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D y z) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K ≫ dgPinchedCompositionFamilyPrism A D f g =
      g ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedHomSlice A D y z := by
  have h := congrArg (fun k => CartesianMonoidalCategory.lift f g ≫ k)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedCompositionPrism_one A D x y z)
  dsimp only [dgPinchedCompositionFamilyPrism]
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint_naturality]
  exact h.trans (congrArg (fun k => k ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedHomSlice A D y z)
    (CartesianMonoidalCategory.lift_snd f g))
/-- 族の実合成 prism の射影は、元の第一族の実区間族。 -/
lemma dgPinchedCompositionFamilyPrism_projection {K : SSet.{max u v}} {x y z : D}
    (f : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D x y) (g : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D y z) :
    dgPinchedCompositionFamilyPrism A D f g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection _ =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y)) := by
  have h := congrArg (fun k => (Δ[1] ◁ CartesianMonoidalCategory.lift f g) ≫ k)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedCompositionPrism_projection A D x y z)
  refine h.trans ?_
  have hw : (Δ[1] ◁ CartesianMonoidalCategory.lift f g) ≫
      (Δ[1] ◁ fst _ _) = (Δ[1] : SSet.{max u v}) ◁ f := by
    rw [← MonoidalCategory.whiskerLeft_comp, CartesianMonoidalCategory.lift_fst]
  have ht := congrArg (fun k => k ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y))) hw
  exact ht.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp f _).symm
/-- 実合成 prism は、任意のパラメータ制限と全時刻で厳密に可換する。 -/
lemma dgPinchedCompositionFamilyPrism_precomp {K L : SSet.{max u v}} {x y z : D}
    (f : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D x y) (g : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D y z) (i : L ⟶ K) :
    (Δ[1] ◁ i) ≫ dgPinchedCompositionFamilyPrism A D f g =
      dgPinchedCompositionFamilyPrism A D (i ≫ f) (i ≫ g) := by
  dsimp only [dgPinchedCompositionFamilyPrism]
  rw [← Category.assoc, ← MonoidalCategory.whiskerLeft_comp, CartesianMonoidalCategory.comp_lift]

end SerrePositivity.InfinityCategories.Project.DerivedCategories
