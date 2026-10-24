module
public import SerrePositivity.InfinityCategories.Derived.Gluing.UniverseExactProjections
public import SerrePositivity.InfinityCategories.Derived.Gluing.LaxComparisonEquivalence
public import SerrePositivity.InfinityCategories.Stable.ExactFunctorChoice
/-!
概要：正本比較は完全同値であり、導来 lax pullback は元 dg gluing と同じ安定性を持つ。
方針：構成済みの実同値で安定性を移し、元の二射影の完全性を逆比較と余単位で戻す。
規約：比較の全単体と元の二射影を保持する。二脚の完全性を新しい入力にしない。
使われ方：F2 の安定 lax pullback と半直交分解の比較に用いる。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)
lemma dgGluingUniverseDerivedNerveLaxComparison_isExactFunctor :
    IsExactFunctor (dgGluingUniverseDerivedNerveLaxComparison R C D M) :=
  isExactFunctor_of_isQCatEquivalence
    (dgGluingUniverseDerivedNerveLaxComparison_isQCatEquivalence R C D M)
lemma dgGluingUniverseDerivedNerveLaxEquivalence_inv_isExactFunctor :
    IsExactFunctor (dgGluingUniverseDerivedNerveLaxEquivalence R C D M).inv :=
  isExactFunctor_of_isQCatEquivalence
    (dgGluingUniverseDerivedNerveLaxEquivalence R C D M).symm.isQCatEquivalence

variable [Small.{u} D] (hC : IsDGPretriangulated R C) (hD : IsDGPretriangulated R D)
include hC hD
lemma dgGluingUniverseDerivedLaxPullback_isStable :
    IsStable (F2.laxPullback (dgGluingUniverseDerivedYoneda.{u,v,w} R C)
      (dgGluingUniverseDerivedCoefficient R C D M)) :=
  (dgGluingUniverseDerivedNerveLaxEquivalence R C D M).isStable_iff.mp
    (dgGluingUniverseNerve_isStable R C D M hC hD)

lemma dgGluingUniverseDerivedLaxPullbackFst_isExactFunctor :
    IsExactFunctor (F2.laxPullbackFst (dgGluingUniverseDerivedYoneda.{u,v,w} R C)
      (dgGluingUniverseDerivedCoefficient R C D M)) := by
  let := dgGluingUniverseLeftNerve_isExactFunctor R C D M hC hD
  let := dgGluingUniverseDerivedNerveLaxEquivalence_inv_isExactFunctor R C D M
  let e := dgGluingUniverseDerivedNerveLaxEquivalence R C D M
  have hi := e.invHomIso.postcomp
    (F2.laxPullbackFst (dgGluingUniverseDerivedYoneda.{u,v,w} R C)
      (dgGluingUniverseDerivedCoefficient R C D M))
  simp only [e, Category.assoc, dgGluingUniverseDerivedNerveLaxEquivalence_hom,
    dgGluingUniverseDerivedNerveLaxComparison_fst, Category.id_comp] at hi
  exact isExactFunctor_of_functorIso hi

lemma dgGluingUniverseDerivedLaxPullbackSnd_isExactFunctor :
    IsExactFunctor (F2.laxPullbackSnd (dgGluingUniverseDerivedYoneda.{u,v,w} R C)
      (dgGluingUniverseDerivedCoefficient R C D M)) := by
  let := dgGluingUniverseRightNerve_isExactFunctor R C D M hC hD
  let := dgGluingUniverseDerivedNerveLaxEquivalence_inv_isExactFunctor R C D M
  let e := dgGluingUniverseDerivedNerveLaxEquivalence R C D M
  have hi := e.invHomIso.postcomp
    (F2.laxPullbackSnd (dgGluingUniverseDerivedYoneda.{u,v,w} R C)
      (dgGluingUniverseDerivedCoefficient R C D M))
  simp only [e, Category.assoc, dgGluingUniverseDerivedNerveLaxEquivalence_hom,
    dgGluingUniverseDerivedNerveLaxComparison_snd, Category.id_comp] at hi
  exact isExactFunctor_of_functorIso hi
end SerrePositivity.InfinityCategories
