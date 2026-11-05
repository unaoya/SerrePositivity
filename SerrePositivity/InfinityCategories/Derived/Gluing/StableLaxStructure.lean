module
public import SerrePositivity.InfinityCategories.Derived.Gluing.StableFactorKernels
public import SerrePositivity.KST.LocalizingInvariants.LaxSemiorthogonal
public import SerrePositivity.InfinityCategories.Derived.DGSemifreeProjectiveEquivalence
/-!
概要：正本比較の標的に、K-8b の元の半直交分解と射影核を接続する。
方針：元の二脚を同じ安定圏の完全射に束ね、公開済みの lax 半直交分解を適用する。
規約：二脚の完全性は上流供給待ちの明示入力であり、無条件の主定理とは扱わない。
使われ方：二脚の完全性が供給された後の、Tamme の分裂と native 因子の照合に用いる。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet KST.LocalizingInvariants
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
def dgGluingStableModuleCategory : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{max (u + 1) v w} where
  _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.obj := (SSet.uliftFunctor.{max (u + 1) v w,max (u + 1) v}).obj
    (dgModuleDerivedInfinityCategory R C)
  _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.isQuasicategory := inferInstance
  _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.isStable := by
    let := dgModuleDerivedInfinityCategory_isStable R C
    exact F2.Idempotent.isStable_ulift
variable (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
  (hC : IsDGPretriangulated R C) (hD : IsDGPretriangulated R D)
  (hY : IsExactFunctor (dgGluingUniverseDerivedYoneda.{u, v, w} R C))
  (hM : IsExactFunctor (dgGluingUniverseDerivedCoefficient R C D M))
def dgGluingStableYonedaMap : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap (dgGluingStableInput.{u, v, w} R C hC)
    (dgGluingStableModuleCategory.{u, v, w} R C) :=
  ⟨dgGluingUniverseDerivedYoneda R C, hY⟩
def dgGluingStableCoefficientMap : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap (dgGluingStableInput.{u, w, v} R D hD)
    (dgGluingStableModuleCategory.{u, v, w} R C) :=
  ⟨dgGluingUniverseDerivedCoefficient R C D M, hM⟩
lemma dgGluingStableLaxObject_eq_laxCategory :
    dgGluingStableLaxObject R C D M hC hD =
      laxCategory (dgGluingStableYonedaMap R C hC hY)
        (dgGluingStableCoefficientMap R C D M hD hM) := rfl
def dgGluingLaxSemiorthogonal :
    _root_.SerrePositivity.InfinityCategories.Stable.Semiorthogonal.SemiorthogonalDecomposition (dgGluingStableInput.{u, w, v} R D hD)
      (dgGluingStableInput.{u, v, w} R C hC) (dgGluingStableLaxObject R C D M hC hD) :=
  laxSemiorthogonal (dgGluingStableYonedaMap R C hC hY)
    (dgGluingStableCoefficientMap R C D M hD hM)
lemma dgGluingLaxSemiorthogonal_projection :
    (dgGluingLaxSemiorthogonal R C D M hC hD hY hM).projection =
      dgGluingStableLaxFst R C D M hC hD := _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap.ext rfl
lemma dgGluingLaxSemiorthogonal_retraction :
    (dgGluingLaxSemiorthogonal R C D M hC hD hY hM).retraction =
      dgGluingStableLaxSnd R C D M hC hD := _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap.ext rfl
lemma dgGluingDFactor_iff_laxSemiorthogonal_image (X : DGGluingObject R C D M) :
    dgGluingFactorIsZero R C X.left ↔
      (dgGluingUniverseDerivedNerveLaxComparison R C D M).app (Opposite.op ⦋0⦌)
        (ULift.up (Simplex.vertex X)) ∈
          _root_.SerrePositivity.InfinityCategories.Stable.Verdier.essentialImage (dgGluingLaxSemiorthogonal R C D M hC hD hY hM).inclusion := by
  rw [dgGluingDFactor_iff_stableLeftKernel]
  have h := (dgGluingLaxSemiorthogonal R C D M hC hD hY hM).kernel
    ((dgGluingUniverseDerivedNerveLaxComparison R C D M).app (Opposite.op ⦋0⦌)
      (ULift.up (Simplex.vertex X)))
  rw [dgGluingLaxSemiorthogonal_projection] at h
  change IsZeroVertex ((dgGluingUniverseDerivedNerveLaxComparison R C D M ≫
    F2.laxPullbackFst (dgGluingUniverseDerivedYoneda.{u, v, w} R C)
      (dgGluingUniverseDerivedCoefficient R C D M)).app (Opposite.op ⦋0⦌)
        (ULift.up (Simplex.vertex X))) ↔ _ at h
  rwa [dgGluingUniverseDerivedNerveLaxComparison_fst] at h
end SerrePositivity.InfinityCategories
