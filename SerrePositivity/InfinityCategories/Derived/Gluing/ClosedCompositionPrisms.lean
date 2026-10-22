module
public import SerrePositivity.InfinityCategories.Derived.Gluing.ClosedPostcompositionAW
public import SerrePositivity.InfinityCategories.Derived.DGPinchedCompositionFamilyPrism

/-! 閉射による実前後合成三角形を、標的小ささなしに全パラメータ・両端・射影付きで保持する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded MonoidalCategory DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D]
  {K : SSet.{max u v}} {x y z : D}

def dgGluingClosedPrecompositionPrism
    (s : ForgetEnrichment.of (Complex R) x ⟶ ForgetEnrichment.of (Complex R) y)
    (g : K ⟶ DGNerve.pinchedHom R D y z) :=
  dgPinchedCompositionFamilyPrism R D (SSet.const (pinchedClosedVertex R D s)) g

lemma dgGluingClosedPrecompositionPrism_zero
    (s : ForgetEnrichment.of (Complex R) x ⟶ ForgetEnrichment.of (Complex R) y)
    (g : K ⟶ DGNerve.pinchedHom R D y z) :
    prismEndpoint 0 K ≫ dgGluingClosedPrecompositionPrism R D s g =
      g ≫ pinchedHomChainMap (D := D) (E := D)
        (eHomWhiskerRight (Complex R) s (ForgetEnrichment.of (Complex R) z)) ≫
          dgPinchedHomSlice R D x z := by
  rw [dgGluingClosedPrecompositionPrism, dgPinchedCompositionFamilyPrism_zero,
    dgGluingPinchedCompositionFamily_closed_pre, Category.assoc]

lemma dgGluingClosedPrecompositionPrism_one
    (s : ForgetEnrichment.of (Complex R) x ⟶ ForgetEnrichment.of (Complex R) y)
    (g : K ⟶ DGNerve.pinchedHom R D y z) :
    prismEndpoint 1 K ≫ dgGluingClosedPrecompositionPrism R D s g =
      g ≫ dgPinchedHomSlice R D y z :=
  dgPinchedCompositionFamilyPrism_one R D _ g

lemma dgGluingClosedPrecompositionPrism_projection
    (s : ForgetEnrichment.of (Complex R) x ⟶ ForgetEnrichment.of (Complex R) y)
    (g : K ⟶ DGNerve.pinchedHom R D y z) :
    dgGluingClosedPrecompositionPrism R D s g ≫ sliceOverProjection _ =
      intervalMappingUncurry ((SSet.const (X := K) (pinchedClosedVertex R D s)) ≫
        pinchedHomToIntervalMappingSpace (X := dgNerve R D)
          (Simplex.vertex x) (Simplex.vertex y)) :=
  dgPinchedCompositionFamilyPrism_projection R D _ g

def dgGluingClosedPostcompositionPrism
    (s : ForgetEnrichment.of (Complex R) y ⟶ ForgetEnrichment.of (Complex R) z)
    (f : K ⟶ DGNerve.pinchedHom R D x y) :=
  dgPinchedCompositionFamilyPrism R D f (SSet.const (pinchedClosedVertex R D s))

lemma dgGluingClosedPostcompositionPrism_zero
    (s : ForgetEnrichment.of (Complex R) y ⟶ ForgetEnrichment.of (Complex R) z)
    (f : K ⟶ DGNerve.pinchedHom R D x y) :
    prismEndpoint 0 K ≫ dgGluingClosedPostcompositionPrism R D s f =
      f ≫ pinchedHomChainMap (D := D) (E := D)
        (eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) x) s) ≫
          dgPinchedHomSlice R D x z := by
  rw [dgGluingClosedPostcompositionPrism, dgPinchedCompositionFamilyPrism_zero,
    dgGluingPinchedCompositionFamily_closed_post, Category.assoc]

lemma dgGluingClosedPostcompositionPrism_one
    (s : ForgetEnrichment.of (Complex R) y ⟶ ForgetEnrichment.of (Complex R) z)
    (f : K ⟶ DGNerve.pinchedHom R D x y) :
    prismEndpoint 1 K ≫ dgGluingClosedPostcompositionPrism R D s f =
      (SSet.const (X := K) (pinchedClosedVertex R D s)) ≫ dgPinchedHomSlice R D y z :=
  dgPinchedCompositionFamilyPrism_one R D f _

lemma dgGluingClosedPostcompositionPrism_projection
    (s : ForgetEnrichment.of (Complex R) y ⟶ ForgetEnrichment.of (Complex R) z)
    (f : K ⟶ DGNerve.pinchedHom R D x y) :
    dgGluingClosedPostcompositionPrism R D s f ≫ sliceOverProjection _ =
      intervalMappingUncurry (f ≫ pinchedHomToIntervalMappingSpace (X := dgNerve R D)
        (Simplex.vertex x) (Simplex.vertex y)) :=
  dgPinchedCompositionFamilyPrism_projection R D f _

end SerrePositivity.InfinityCategories
