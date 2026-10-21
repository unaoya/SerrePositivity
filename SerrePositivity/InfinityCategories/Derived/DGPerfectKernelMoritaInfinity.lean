module
public import SerrePositivity.InfinityCategories.Derived.DGPerfectKernelInclusion
public import SerrePositivity.InfinityCategories.Derived.DGPerfectKernelEssentialSurjectivity
public import SerrePositivity.InfinityCategories.Derived.DGKernelMoritaCriterionInfinity
/-!
概要：一般双加群の Morita 同値を元の D・Perf の実 ∞ 圏同値として結論する。
方針：Perf 作用の全写像空間での充満忠実性と実本質的全射性を合わせる。
規約：明示三条件と両側 compact 生成を保つ。使われ方：β5 e の最終結論。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v z z'
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (D E : Type v)
  [DGCategory R D] [Small.{u} D] [DGCategory R E] [Small.{u} E]
/-- 同じ一般 kernel の Morita 同値の perfect 制限。 -/
lemma dgPerfectKernelInfinity_isQCatEquivalence_of_classical
    (P : Bimodule R E D) [(Morita.kernelDerivedTensorOnBimodule R D E P).IsEquivalence] :
    IsQCatEquivalence (dgPerfectKernelInfinity R D E P) :=
  isQCatEquivalence_of_isFullyFaithful_of_isEssentiallySurjective _
    (dgPerfectKernelInfinity_isFullyFaithful R D E P)
    (dgPerfectKernelInfinity_isEssentiallySurjective R D E P)
/-- 同じ一般 kernel の Morita 同値の perfect 制限。 -/
lemma dgPerfectKernelInfinity_isExactFunctor_of_classical
    (P : Bimodule R E D) [(Morita.kernelDerivedTensorOnBimodule R D E P).IsEquivalence] :
    IsExactFunctor (dgPerfectKernelInfinity R D E P) :=
  isExactFunctor_of_isQCatEquivalence
    (dgPerfectKernelInfinity_isQCatEquivalence_of_classical R D E P)
variable (P : Bimodule R E D)
  (hP : Morita.CriterionPerfConditions R D E
    ((bimoduleToDerived R E D).obj (BimoduleCategory.of R E D P)))
  {I : Type z} [Small.{u} I] (G : I → DerivedModuleCategory R D)
  (hG : Morita.CriterionDerivedCompactGeneration R D G)
  {J : Type z'} [Small.{u} J] (H : J → DerivedModuleCategory R E)
  (hH : Morita.CriterionDerivedCompactGeneration R E H)
include hP G hG H hH in
/-- 同じ一般 kernel の Morita 同値の perfect 制限。 -/
lemma dgKernelClassical_isEquivalence_of_morita :
    (Morita.kernelDerivedTensorOnBimodule R D E P).IsEquivalence := by
  have : (Morita.kernelDerivedTensor R D E
      ((bimoduleToDerived R E D).obj (BimoduleCategory.of R E D P))).IsEquivalence :=
    (Morita.kernelMoritaEquivalence R D E _ hP G hG H hH).isEquivalence_functor
  exact Functor.isEquivalence_of_iso
    (Morita.kernelDerivedTensorOnBimoduleIso R D E (BimoduleCategory.of R E D P))
/-- 同じ一般 kernel の Morita 同値の perfect 制限。 -/
def dgMoritaPerfectKernelInfinity :
    dgModulePerfectInfinityCategory R D ⟶ dgModulePerfectInfinityCategory R E := by
  let := dgKernelClassical_isEquivalence_of_morita R D E P hP G hG H hH
  exact dgPerfectKernelInfinity R D E P
/-- 同じ一般 kernel の Morita 同値の perfect 制限。 -/
lemma dgMoritaPerfectKernelInfinity_isQCatEquivalence :
    IsQCatEquivalence (dgMoritaPerfectKernelInfinity R D E P hP G hG H hH) := by
  let := dgKernelClassical_isEquivalence_of_morita R D E P hP G hG H hH
  exact dgPerfectKernelInfinity_isQCatEquivalence_of_classical R D E P
/-- 同じ一般 kernel の Morita 同値の perfect 制限。 -/
lemma dgMoritaPerfectKernelInfinity_isExactFunctor :
    IsExactFunctor (dgMoritaPerfectKernelInfinity R D E P hP G hG H hH) := by
  let := dgKernelClassical_isEquivalence_of_morita R D E P hP G hG H hH
  exact dgPerfectKernelInfinity_isExactFunctor_of_classical R D E P
/-- 同じ一般 kernel の Morita 同値の perfect 制限。 -/
def dgMoritaPerfectKernelInclusionIso :
    FunctorIso (dgMoritaPerfectKernelInfinity R D E P hP G hG H hH ≫
      dgPerfectInclusionInfinity R E)
      (dgPerfectInclusionInfinity R D ≫ dgKernelDerivedInfinity R D E P) := by
  let := dgKernelClassical_isEquivalence_of_morita R D E P hP G hG H hH
  exact dgPerfectKernelInclusionIso R D E P
end SerrePositivity.InfinityCategories
