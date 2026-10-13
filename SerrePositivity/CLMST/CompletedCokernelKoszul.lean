module

public import SerrePositivity.CLMST.CompletedTensorIsogeny
public import SerrePositivity.CLMST.PerfectoidCokernel
public import SerrePositivity.CLMST.StageTensor

/-! # 完備塔上の余核を係数とする有限段の Koszul ホモロジー

isogeny の余核を実際のテンソル代数上で構成し、標準段写像で係数制限する。
一つの消去冪を、全段・任意の列・全次数へ同時に供給する。
この消去だけで正規化長さが零であるとは主張しない。
-/

@[expose] public noncomputable section
universe u
open scoped TensorProduct
namespace SerrePositivity.CLMST
open Section2 CategoryTheory
attribute [local instance] HasDerivedCategory.standard
variable (A D : Type u) [CommRing A] [IsNoetherianRing A]
    [CommRing D] [Algebra A D] [Module.Finite A D]
    {h : ℕ} (t : Fin h → A) (p : ℕ) [Fact p.Prime]
    (hperf : IsIntegralPerfectoid (CompletedTower A t p) p)
local instance : Module.FinitePresentation A D := Module.finitePresentation_of_finite A D

/-- 完備テンソル代数上の余核を有限段へ係数制限した実加群。 -/
abbrev stagePerfectoidCokernel (n : ℕ) : ModuleCat.{u} (StageAlgebra A D t p n) :=
  (ModuleCat.restrictScalars (stageToCompletedTensor A D t p n).toRingHom).obj
    (ModuleCat.of ((CompletedTower A t p) ⊗[A] D)
      (PerfectoidizationCokernel (CompletedTower A t p)
        ((CompletedTower A t p) ⊗[A] D) p hperf))

/-- 標数零の有限整域拡大では、全段・全列・全次数に同じ g の消去冪を供給できる。 -/
theorem exists_uniform_stageCokernel_koszul_annihilator
    [IsDomain D] [CharZero D] (hinj : Function.Injective (algebraMap A D))
    (g : A) (hg : g ≠ 0)
    (hEtale : let _ := GenericEtale.awayAlgebra A D g
      Algebra.Etale (Localization.Away g) (Localization.Away (algebraMap A D g))) :
    ∃ N : ℕ, ∀ (n e : ℕ) (z : Fin e → StageAlgebra A D t p n) (q : ℤ),
      ∀ x : ((koszulModuleFunctor z).obj (stagePerfectoidCokernel A D t p hperf n)).homology q,
        (algebraMap A (StageAlgebra A D t p n) g) ^ N • x = 0 := by
  obtain ⟨_, N, hN⟩ :=
    completedTensor_injective_and_exists_pow_annihilates_coker_of_domain A D t p hperf
      hinj g hg hEtale
  refine ⟨N, fun n e z q ↦ ?_⟩
  apply perfectoidizationCokernel_restricted_koszul_annihilated (CompletedTower A t p)
    ((CompletedTower A t p) ⊗[A] D) p hperf (stageToCompletedTensor A D t p n).toRingHom
    (algebraMap A (CompletedTower A t p) g)
    (algebraMap A (StageAlgebra A D t p n) g) ?_ N hN z q
  exact (stageToCompletedTensor A D t p n).commutes g |>.trans
    (IsScalarTower.algebraMap_apply A (CompletedTower A t p) ((CompletedTower A t p) ⊗[A] D) g)

/-- 標準写像・余核の列を有限段へ制限し、Koszul構成した実際の短完全列。 -/
theorem stagePerfectoidCokernel_koszul_shortExact
    [IsDomain D] [CharZero D] (hinj : Function.Injective (algebraMap A D))
    (g : A) (hg : g ≠ 0)
    (hEtale : let _ := GenericEtale.awayAlgebra A D g
      Algebra.Etale (Localization.Away g) (Localization.Away (algebraMap A D g)))
    (n : ℕ) {e : ℕ} (z : Fin e → StageAlgebra A D t p n) :
    ((algebraMapCokernelShortComplex ((CompletedTower A t p) ⊗[A] D)
        (RPerfd A D t p hperf)).map
      (ModuleCat.restrictScalars (stageToCompletedTensor A D t p n).toRingHom ⋙
        koszulModuleFunctor z)).ShortExact :=
  perfectoidizationCokernel_restricted_koszul_shortExact (CompletedTower A t p)
    ((CompletedTower A t p) ⊗[A] D) p hperf
    (stageToCompletedTensor A D t p n).toRingHom z
    (completedTensor_injective_and_exists_pow_annihilates_coker_of_domain A D t p hperf
      hinj g hg hEtale).1

end SerrePositivity.CLMST
