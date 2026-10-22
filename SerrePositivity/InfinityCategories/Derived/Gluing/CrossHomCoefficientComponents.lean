module
public import SerrePositivity.InfinityCategories.Derived.Gluing.CrossHomCoefficient
public import SerrePositivity.InfinityCategories.Derived.Gluing.CoconeBottomComponents

/-! 実係数包含の両 Hom 射影は零、同じ全整数次数の第三成分は恒等。 -/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits HomologicalComplex CochainComplex DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)
  (X : DGGluingCFactor R C D M) (Y : DGGluingDFactor R C D M)

lemma dgGluingCrossHomCoefficientMap_left :
    dgGluingCrossHomCoefficientMap R C D M X Y ≫
      dgGluingLeftHomMap R C D M X.val Y.val = 0 := by
  simp only [dgGluingCrossHomCoefficientMap, dgGluingLeftHomMap,
    ← Category.assoc, dgGluingCoconeBottomInclusion_fst]
  erw [zero_comp]

lemma dgGluingCrossHomCoefficientMap_right :
    dgGluingCrossHomCoefficientMap R C D M X Y ≫
      dgGluingRightHomMap R C D M X.val Y.val = 0 := by
  simp only [dgGluingCrossHomCoefficientMap, dgGluingRightHomMap,
    ← Category.assoc, dgGluingCoconeBottomInclusion_fst]
  erw [zero_comp]

lemma dgGluingCrossHomCoefficientMap_primitive (n : ℤ) :
    (dgGluingCrossHomCoefficientMap R C D M X Y).f n ≫
      (dgGluingHomPrimitive R C D M X.val Y.val).v n (n - 1) (by omega) = 𝟙 _ :=
  dgGluingCoconeBottomInclusion_snd (dgGluingDifference R C D M X.val Y.val) n

end SerrePositivity.InfinityCategories
