import SerrePositivity.CLMST.Prop247FiniteFreeComparison
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.Util.AssertNoSorry

assert_no_sorry SerrePositivity.exists_away_comparison_of_finitePresentation
assert_no_sorry SerrePositivity.CLMST.prop247_exists_finiteFree_comparison_of_tensor_equiv
#print axioms SerrePositivity.exists_away_comparison_of_finitePresentation
#print axioms SerrePositivity.CLMST.prop247_exists_finiteFree_comparison_of_tensor_equiv

universe u
open SerrePositivity SerrePositivity.CLMST
open scoped TensorProduct
attribute [local instance] HasDerivedCategory.standard

-- 原典の有限かつ代数有限表示の仮定から、実局所代数同型をそのまま使えることを確認する。
theorem audit_prop247_finite_algebra_splitting
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] [IsReduced R]
    [Module.Finite R S] [Algebra.FinitePresentation R S] (g : R) (r : ℕ)
    (e : (Localization.Away g) ⊗[R] S ≃ₐ[Localization.Away g]
      (Fin r → Localization.Away g)) :
    ∃ u : S →ₗ[R] (Fin r → R), Function.Bijective (awayModuleMap g u) ∧
      ∃ q : ℕ, moduleMapConeScalar R u (g ^ q) = 0 := by
  let := Module.FinitePresentation.of_finite_of_finitePresentation R S
  obtain ⟨_k, u, _he, hu, q, hq, _hk, _hc⟩ :=
    prop247_exists_finiteFree_comparison_of_tensor_equiv g (Localization.Away g) r e.toLinearEquiv
  exact ⟨u, hu, q, hq⟩

assert_no_sorry audit_prop247_finite_algebra_splitting
#print axioms audit_prop247_finite_algebra_splitting
