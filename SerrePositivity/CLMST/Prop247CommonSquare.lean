module

public import SerrePositivity.CLMST.Prop247FiniteFreeComparison
public import SerrePositivity.CommutativeAlgebra.PerfectoidizationAlgebraMap
public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation

/-! # Prop 2.4.7：局所分裂の元の共通対象での可換図式

有限表示性で分母を払った比較写像に、有限性で一つの追加の冪を掛ける。
共通対象から局所化への写像は単射でなくてよい。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.CLMST
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- 元の共通対象への二つの写像と局所分裂から、共通対象内で厳密に可換な
有限自由比較を作る。almost 比較や perfectoid 化の引用を要求しない。 -/
theorem prop247_exists_common_square_of_localized_splitting
    {R M E : Type u} [CommRing R] [IsReduced R]
    [AddCommGroup M] [Module R M] [Module.FinitePresentation R M]
    [AddCommGroup E] [Module R E]
    (d : R) (L : Type u) [CommRing L] [Algebra R L] [IsLocalization (.powers d) L]
    (r : ℕ) (e : L ⊗[R] M ≃ₗ[L] (Fin r → L))
    (a : M →ₗ[R] E) (b : (Fin r → R) →ₗ[R] E)
    (l : E →ₗ[R] (Fin r → L)) [IsLocalizedModule (.powers d) l]
    (ha : ∀ x, l (a x) = e ((1 : L) ⊗ₜ[R] x))
    (hb : ∀ z i, l (b z) i = algebraMap R L (z i)) :
    ∃ (k : ℕ) (u : M →ₗ[R] (Fin r → R)),
      (d ^ k • a = b.comp u) ∧
      (∀ x i, algebraMap R L (u x i) =
        (algebraMap R L d) ^ k * e ((1 : L) ⊗ₜ[R] x) i) ∧
      Function.Bijective (awayModuleMap d u) ∧
      ∃ q : ℕ, moduleMapConeScalar R u (d ^ q) = 0 ∧
        (∀ x : u.ker, d ^ q • x = 0) ∧
        (∀ y : (Fin r → R) ⧸ u.range, d ^ q • y = 0) := by
  obtain ⟨k, u, he, hu, _hq⟩ :=
    prop247_exists_finiteFree_comparison_of_tensor_equiv d L r e
  have hs : l.comp (d ^ k • a) = l.comp (b.comp u) := by
    ext x i
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, map_smul, ha, Pi.smul_apply,
      Algebra.smul_def, map_pow, hb, he]
  obtain ⟨s, hs⟩ := Module.Finite.exists_smul_of_comp_eq_of_isLocalizedModule
    (.powers d) l (d ^ k • a) (b.comp u) hs
  obtain ⟨m, hm⟩ := s.property
  have hsq : d ^ (m + k) • a = b.comp (d ^ m • u) := by
    simpa only [Submonoid.smul_def, ← hm, smul_smul, ← pow_add, LinearMap.comp_smul] using hs
  have hu' : Function.Bijective (awayModuleMap d (d ^ m • u)) := by
    change Function.Bijective
      (IsLocalizedModule.map (.powers d) _ _ (d ^ m • u))
    rw [map_smul]
    exact ((Module.End.isUnit_iff _).mp (IsLocalizedModule.map_units
      (LocalizedModule.mkLinearMap (.powers d) (Fin r → R))
      (⟨d ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers d))).comp hu
  refine ⟨m + k, d ^ m • u, hsq, ?_, hu',
    finiteFreeConeIsogeny_with_annihilators R d r (d ^ m • u) hu'⟩
  intro x i
  change algebraMap R L (d ^ m • u x i) = _
  change algebraMap R L (d ^ m * u x i) = _
  rw [map_mul, map_pow, he, pow_add, mul_assoc]

/-- 指定した perfectoid 化とその元の誘導写像に、前の厳密可換式を渡す。
誘導写像を不特定の比較写像に置き換えず、必要な分母の冪を明示する。 -/
theorem prop247_exists_perfectoid_common_square
    {R A E P Q : Type u} [CommRing R] [IsReduced R] [CommRing A] [CommRing E]
    [CommRing P] [CommRing Q] [Algebra R A] [Algebra R E] [Algebra R P] [Algebra R Q]
    [Module.Finite R A] [Algebra.FinitePresentation R A]
    (p : ℕ) [Fact p.Prime]
    (β : A →ₐ[R] P) (hβ : IsPerfectoidization p β.toRingHom)
    (η : E →ₐ[R] Q) (hη : IsPerfectoidization p η.toRingHom)
    (d : R) (L : Type u) [CommRing L] [Algebra R L] [IsLocalization (.powers d) L]
    (r : ℕ) (e : L ⊗[R] A ≃ₐ[L] (Fin r → L))
    (a : A →ₐ[R] E) (b : (Fin r → R) →ₐ[R] E)
    (l : E →ₐ[R] (Fin r → L)) [IsLocalizedModule (.powers d) l.toLinearMap]
    (ha : ∀ x, l (a x) = e ((1 : L) ⊗ₜ[R] x))
    (hb : ∀ z i, l (b z) i = algebraMap R L (z i)) :
    ∃ (k : ℕ) (u : A →ₗ[R] (Fin r → R)),
      (d ^ k • (IsPerfectoidization.mapAlgHom hβ hη a).toLinearMap).comp β.toLinearMap =
        (η.comp b).toLinearMap.comp u ∧
      Function.Bijective (awayModuleMap d u) ∧
      ∃ q : ℕ, moduleMapConeScalar R u (d ^ q) = 0 ∧
        (∀ x : u.ker, d ^ q • x = 0) ∧
        (∀ y : (Fin r → R) ⧸ u.range, d ^ q • y = 0) := by
  let := Module.FinitePresentation.of_finite_of_finitePresentation R A
  obtain ⟨k, u, hsq, _he, hu, hq⟩ :=
    prop247_exists_common_square_of_localized_splitting d L r e.toLinearEquiv
      a.toLinearMap b.toLinearMap l.toLinearMap ha hb
  refine ⟨k, u, ?_, hu, hq⟩
  have hmap := IsPerfectoidization.mapAlgHom_comp hβ hη a
  ext x
  have hx := LinearMap.congr_fun hsq x
  change d ^ k • a x = b (u x) at hx
  change d ^ k • IsPerfectoidization.mapAlgHom hβ hη a (β x) = η (b (u x))
  have hmx : IsPerfectoidization.mapAlgHom hβ hη a (β x) = η (a x) :=
    AlgHom.congr_fun hmap x
  rw [hmx]
  exact (η.toLinearMap.map_smul (d ^ k) (a x)).symm.trans (congrArg η hx)

end SerrePositivity.CLMST
