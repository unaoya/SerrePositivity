module
public import SerrePositivity.InfinityCategories.Derived.Gluing.StableLaxStructure
public import SerrePositivity.InfinityCategories.Derived.Gluing.StableTammeComparison
public import SerrePositivity.InfinityCategories.Derived.QCatEquivalenceAdjunction
/-!
概要：K-8b の実半直交分解を、元 dg gluing の共通宇宙の nerve へ戻す。
方針：元の比較同値と実随伴を合成し、元射影を両射影の厳密な比較式で回収する。
規約：二脚の完全性は上流供給待ちの明示入力。因子の順序は ⟨D,C⟩ を保つ。
使われ方：native gluing の分解と Tamme の分裂との整合に用いる。
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
  (hY : IsExactFunctor (dgGluingUniverseDerivedYoneda.{u, v, w} R C))
  (hM : IsExactFunctor (dgGluingUniverseDerivedCoefficient R C D M))
def dgGluingNativeDInclusion : ExactMap (dgGluingStableInput.{u, w, v} R D hD)
    (dgGluingStableObject R C D M hC hD) :=
  ⟨(dgGluingLaxSemiorthogonal R C D M hC hD hY hM).inclusion.hom ≫
    (dgGluingStableComparisonInverse R C D M hC hD).hom, inferInstance⟩
def dgGluingNativeCInclusion : ExactMap (dgGluingStableInput.{u, v, w} R C hC)
    (dgGluingStableObject R C D M hC hD) :=
  ⟨(dgGluingLaxSemiorthogonal R C D M hC hD hY hM).rightInclusion.hom ≫
    (dgGluingStableComparisonInverse R C D M hC hD).hom, inferInstance⟩
def dgGluingNativeRightAdjunction :
    QCatAdjunction (dgGluingUniverseLeftNerve R C D M)
      (dgGluingNativeCInclusion R C D M hC hD hY hM).hom := by
  have a := (dgGluingUniverseDerivedNerveLaxEquivalence R C D M).toAdjunction.comp
    (dgGluingLaxSemiorthogonal R C D M hC hD hY hM).rightAdjunction
  change QCatAdjunction (dgGluingUniverseDerivedNerveLaxComparison R C D M ≫
    F2.laxPullbackFst (dgGluingUniverseDerivedYoneda.{u, v, w} R C)
      (dgGluingUniverseDerivedCoefficient R C D M)) _ at a
  rwa [dgGluingUniverseDerivedNerveLaxComparison_fst] at a
def dgGluingNativeLeftAdjunction :
    QCatAdjunction (dgGluingNativeDInclusion R C D M hC hD hY hM).hom
      (dgGluingUniverseRightNerve R C D M) := by
  have a := (dgGluingLaxSemiorthogonal R C D M hC hD hY hM).leftAdjunction.comp
    (dgGluingUniverseDerivedNerveLaxEquivalence R C D M).symm.toAdjunction
  change QCatAdjunction _ (dgGluingUniverseDerivedNerveLaxComparison R C D M ≫
    F2.laxPullbackSnd (dgGluingUniverseDerivedYoneda.{u, v, w} R C)
      (dgGluingUniverseDerivedCoefficient R C D M)) at a
  rwa [dgGluingUniverseDerivedNerveLaxComparison_snd] at a
end SerrePositivity.InfinityCategories
