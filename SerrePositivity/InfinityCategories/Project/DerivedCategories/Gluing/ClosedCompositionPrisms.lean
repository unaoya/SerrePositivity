module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ClosedPostcompositionAW
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGPinchedCompositionFamilyPrism

/-! 閉射による実前後合成三角形を、標的小ささなしに全パラメータ・両端・射影付きで保持する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded MonoidalCategory SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D]
  {K : SSet.{max u v}} {x y z : D}

def dgGluingClosedPrecompositionPrism
    (s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) x ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) y)
    (g : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom R D y z) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedCompositionFamilyPrism R D (SSet.const (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedVertex R D s)) g

lemma dgGluingClosedPrecompositionPrism_zero
    (s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) x ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) y)
    (g : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom R D y z) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 K ≫ dgGluingClosedPrecompositionPrism R D s g =
      g ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap (D := D) (E := D)
        (eHomWhiskerRight (_root_.SerrePositivity.DifferentialGraded.Complex R) s (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) z)) ≫
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedHomSlice R D x z := by
  rw [dgGluingClosedPrecompositionPrism, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedCompositionFamilyPrism_zero,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPinchedCompositionFamily_closed_pre, Category.assoc]

lemma dgGluingClosedPrecompositionPrism_one
    (s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) x ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) y)
    (g : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom R D y z) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K ≫ dgGluingClosedPrecompositionPrism R D s g =
      g ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedHomSlice R D y z :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedCompositionFamilyPrism_one R D _ g

lemma dgGluingClosedPrecompositionPrism_projection
    (s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) x ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) y)
    (g : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom R D y z) :
    dgGluingClosedPrecompositionPrism R D s g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection _ =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry ((SSet.const (X := K) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedVertex R D s)) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R D)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y)) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedCompositionFamilyPrism_projection R D _ g

def dgGluingClosedPostcompositionPrism
    (s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) y ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) z)
    (f : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom R D x y) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedCompositionFamilyPrism R D f (SSet.const (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedVertex R D s))

lemma dgGluingClosedPostcompositionPrism_zero
    (s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) y ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) z)
    (f : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom R D x y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 K ≫ dgGluingClosedPostcompositionPrism R D s f =
      f ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap (D := D) (E := D)
        (eHomWhiskerLeft (_root_.SerrePositivity.DifferentialGraded.Complex R) (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) x) s) ≫
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedHomSlice R D x z := by
  rw [dgGluingClosedPostcompositionPrism, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedCompositionFamilyPrism_zero,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPinchedCompositionFamily_closed_post, Category.assoc]

lemma dgGluingClosedPostcompositionPrism_one
    (s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) y ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) z)
    (f : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom R D x y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K ≫ dgGluingClosedPostcompositionPrism R D s f =
      (SSet.const (X := K) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedVertex R D s)) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedHomSlice R D y z :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedCompositionFamilyPrism_one R D f _

lemma dgGluingClosedPostcompositionPrism_projection
    (s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) y ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) z)
    (f : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom R D x y) :
    dgGluingClosedPostcompositionPrism R D s f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection _ =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R D)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y)) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedCompositionFamilyPrism_projection R D f _

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
