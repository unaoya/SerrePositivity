module
public import SerrePositivity.InfinityCategories.Derived.Gluing.OrdinaryPullbackEquivalence
/-!
概要：通常 pullback の dg 模型の安定性と元 gluing への実完全包含。
方針：通常 pullback の安定性を正本比較同値で戻し、完全包含を余単位で照合する。
規約：包含は元の充満 dg 包含の全単体写像である。
使われ方：同じ部分圏を零化する Verdier 商と二射影の接続に用いる。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet KST.LocalizingInvariants
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
  (hC : IsDGPretriangulated R C) (hD : IsDGPretriangulated R D)
include hC hD
lemma dgGluingCanonicalOrdinaryPullback_isStable :
    IsStable (F2.catPullback (dgGluingUniverseDerivedYoneda.{u, v, w} R C)
      (dgGluingUniverseDerivedCoefficient R C D M)) :=
  (pullbackCategory
    (dgGluingStableYonedaMap R C hC
      (dgGluingUniverseDerivedYoneda_isExactFunctor.{u, v, w} R C hC))
    (dgGluingStableCoefficientMap R C D M hD
      (dgGluingUniverseDerivedCoefficient_isExactFunctor R C D M hD))).isStable
lemma dgGluingPullbackUniverseNerve_isStable :
    IsStable ((SSet.uliftFunctor.{max (u + 1) v w, max u v w}).obj
      (dgNerve R (DGGluingPullbackObject R C D M))) :=
  (dgGluingOrdinaryPullbackEquivalence R C D M hC hD).isStable_iff.mpr
    (dgGluingCanonicalOrdinaryPullback_isStable R C D M hC hD)
lemma dgGluingOrdinaryPullbackComparison_isExactFunctor :
    IsExactFunctor (dgGluingOrdinaryPullbackComparison R C D M) :=
  isExactFunctor_of_isQCatEquivalence
    (dgGluingOrdinaryPullbackComparison_isQCatEquivalence R C D M hC hD)
lemma dgGluingPullbackToLax_isExactFunctor :
    IsExactFunctor (dgGluingPullbackToLax R C D M) := by
  let p := dgGluingStableYonedaMap R C hC
    (dgGluingUniverseDerivedYoneda_isExactFunctor.{u, v, w} R C hC)
  let q := dgGluingStableCoefficientMap R C D M hD
    (dgGluingUniverseDerivedCoefficient_isExactFunctor R C D M hD)
  let := dgGluingOrdinaryPullbackComparison_isExactFunctor R C D M hC hD
  have : IsExactFunctor (F2.catPullbackToLax (dgGluingUniverseDerivedYoneda.{u, v, w} R C)
      (dgGluingUniverseDerivedCoefficient R C D M)) :=
    pullbackComparison_isExact p q
  rw [← dgGluingOrdinaryPullbackComparison_toLax]
  exact isExactFunctor_comp _ _
lemma dgGluingPullbackUniverseInclusion_isExactFunctor :
    IsExactFunctor (dgGluingPullbackUniverseInclusion R C D M) := by
  let : IsExactFunctor (dgGluingPullbackUniverseInclusion R C D M ≫
      dgGluingUniverseDerivedNerveLaxComparison R C D M) :=
    dgGluingPullbackToLax_isExactFunctor R C D M hC hD
  let := dgGluingUniverseDerivedNerveLaxEquivalence_inv_isExactFunctor R C D M
  let e := dgGluingUniverseDerivedNerveLaxEquivalence R C D M
  have hi := e.homInvIso.precomp (dgGluingPullbackUniverseInclusion R C D M)
  simp only [e, ← Category.assoc, dgGluingUniverseDerivedNerveLaxEquivalence_hom,
    Category.comp_id] at hi
  exact isExactFunctor_of_functorIso hi
def dgGluingPullbackStableObject : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{max (u + 1) v w} where
  obj := (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).obj
    (dgNerve R (DGGluingPullbackObject R C D M))
  isQuasicategory := inferInstance
  isStable := dgGluingPullbackUniverseNerve_isStable R C D M hC hD
def dgGluingPullbackStableInclusion :
    _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap (dgGluingPullbackStableObject R C D M hC hD)
      (dgGluingStableObject R C D M hC hD) :=
  ⟨dgGluingPullbackUniverseInclusion R C D M,
    dgGluingPullbackUniverseInclusion_isExactFunctor R C D M hC hD⟩
end SerrePositivity.InfinityCategories
