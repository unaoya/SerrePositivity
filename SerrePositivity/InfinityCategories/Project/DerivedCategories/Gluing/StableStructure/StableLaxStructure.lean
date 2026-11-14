module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.StableStructure.StableFactorKernels
public import SerrePositivity.KST.LocalizingInvariants.LaxSemiorthogonal
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.Resolutions.DGSemifreeProjectiveEquivalence
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded SSet KST.LocalizingInvariants
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [Small.{u} C]
def dgGluingStableModuleCategory : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{max (u + 1) v w} where
  obj := (SSet.uliftFunctor.{max (u + 1) v w,max (u + 1) v}).obj
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R C)
  isQuasicategory := inferInstance
  isStable := by
    let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory_isStable R C
    exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Idempotent.isStable_ulift
variable (D : Type w) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D] (M : _root_.SerrePositivity.DifferentialGraded.Bimodule R C D)
  (hC : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R C) (hD : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R D)
  (hY : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedYoneda.{u, v, w} R C))
  (hM : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedCoefficient R C D M))
def dgGluingStableYonedaMap : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingStableInput.{u, v, w} R C hC)
    (dgGluingStableModuleCategory.{u, v, w} R C) :=
  ⟨_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedYoneda R C, hY⟩
def dgGluingStableCoefficientMap : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingStableInput.{u, w, v} R D hD)
    (dgGluingStableModuleCategory.{u, v, w} R C) :=
  ⟨_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedCoefficient R C D M, hM⟩
lemma dgGluingStableLaxObject_eq_laxCategory :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingStableLaxObject R C D M hC hD =
      laxCategory (dgGluingStableYonedaMap R C hC hY)
        (dgGluingStableCoefficientMap R C D M hD hM) := rfl
def dgGluingLaxSemiorthogonal :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Semiorthogonal.SemiorthogonalDecomposition (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingStableInput.{u, w, v} R D hD)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingStableInput.{u, v, w} R C hC) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingStableLaxObject R C D M hC hD) :=
  laxSemiorthogonal (dgGluingStableYonedaMap R C hC hY)
    (dgGluingStableCoefficientMap R C D M hD hM)
lemma dgGluingLaxSemiorthogonal_projection :
    (dgGluingLaxSemiorthogonal R C D M hC hD hY hM).projection =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingStableLaxFst R C D M hC hD := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap.ext rfl
lemma dgGluingLaxSemiorthogonal_retraction :
    (dgGluingLaxSemiorthogonal R C D M hC hD hY hM).retraction =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingStableLaxSnd R C D M hC hD := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap.ext rfl
lemma dgGluingDFactor_iff_laxSemiorthogonal_image (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFactorIsZero R C X.left ↔
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedNerveLaxComparison R C D M).app (Opposite.op ⦋0⦌)
        (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X)) ∈
          _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.essentialImage (dgGluingLaxSemiorthogonal R C D M hC hD hY hM).inclusion := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDFactor_iff_stableLeftKernel]
  have h := (dgGluingLaxSemiorthogonal R C D M hC hD hY hM).kernel
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedNerveLaxComparison R C D M).app (Opposite.op ⦋0⦌)
      (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X)))
  rw [dgGluingLaxSemiorthogonal_projection] at h
  change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedNerveLaxComparison R C D M ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackFst (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedYoneda.{u, v, w} R C)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedCoefficient R C D M)).app (Opposite.op ⦋0⦌)
        (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X))) ↔ _ at h
  rwa [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedNerveLaxComparison_fst] at h
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
