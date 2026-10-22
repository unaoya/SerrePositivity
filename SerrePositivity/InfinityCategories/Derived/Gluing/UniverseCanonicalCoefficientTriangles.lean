module
public import SerrePositivity.InfinityCategories.Derived.Gluing.CanonicalDerivedCoefficientTriangleRecovery
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomDerivedCoefficientTriangles

/-! 主比較に使う共通宇宙・全 gluing Hom 上の二三角形を、同じ native prism の具体的な族へ正規化。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory DifferentialGraded
open scoped Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)

lemma dgGluingUniverseDerivedLeftCoefficientTriangleFamily_canonical
    (X Y : DGGluingObject R C D M) :
    dgGluingUniverseDerivedLeftCoefficientTriangleFamily R C D M X Y =
      dgGluingUniverseModuleDerivedSimplexFamily.{u, v, w} R C
        (homObject R C X.left Y.left) 2
        (dgGluingCanonicalDerivedLeftCoefficientTriangleFamily R C D M X Y) := by
  rw [dgGluingUniverseDerivedLeftCoefficientTriangleFamily,
    dgGluingModuleDerivedLeftCoefficientTriangleFamily_canonical R C D M X Y]

lemma dgGluingUniverseDerivedRightCoefficientTriangleFamily_canonical
    (X Y : DGGluingObject R C D M) :
    dgGluingUniverseDerivedRightCoefficientTriangleFamily R C D M X Y =
      dgGluingUniverseModuleDerivedSimplexFamily.{u, v, w} R C
        (homObject R D X.right Y.right) 2
        (dgGluingCanonicalDerivedRightCoefficientTriangleFamily R C D M X Y) := by
  rw [dgGluingUniverseDerivedRightCoefficientTriangleFamily,
    dgGluingModuleDerivedRightCoefficientTriangleFamily_canonical R C D M X Y]

lemma dgGluingHomDerivedLeftCoefficientTriangle_canonical (X Y : DGGluingObject R C D M) :
    dgGluingHomDerivedLeftCoefficientTriangle R C D M X Y =
      ((Δ[2] : SSet.{max (u + 1) v w}) ◁
        (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).map
          (complexPinchedMap.{u, max u v w} (dgGluingLeftHomMap R C D M X Y))) ≫
        dgGluingUniverseModuleDerivedSimplexFamily.{u, v, w} R C
          (homObject R C X.left Y.left) 2
          (dgGluingCanonicalDerivedLeftCoefficientTriangleFamily R C D M X Y) := by
  rw [dgGluingHomDerivedLeftCoefficientTriangle,
    dgGluingUniverseDerivedLeftCoefficientTriangleFamily_canonical R C D M X Y]

lemma dgGluingHomDerivedRightCoefficientTriangle_canonical (X Y : DGGluingObject R C D M) :
    dgGluingHomDerivedRightCoefficientTriangle R C D M X Y =
      ((Δ[2] : SSet.{max (u + 1) v w}) ◁
        (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).map
          (complexPinchedMap.{u, max u v w} (dgGluingRightHomMap R C D M X Y))) ≫
        dgGluingUniverseModuleDerivedSimplexFamily.{u, v, w} R C
          (homObject R D X.right Y.right) 2
          (dgGluingCanonicalDerivedRightCoefficientTriangleFamily R C D M X Y) := by
  rw [dgGluingHomDerivedRightCoefficientTriangle,
    dgGluingUniverseDerivedRightCoefficientTriangleFamily_canonical R C D M X Y]

end SerrePositivity.InfinityCategories
