module

public import SerrePositivity.CommutativeAlgebra.RankLocus
public import SerrePositivity.CommutativeAlgebra.Localization.PowerTorsion
public import SerrePositivity.CommutativeAlgebra.ScalarIsogeny
public import SerrePositivity.HomologicalAlgebra.ScalarConeAnnihilators
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.TensorProduct.IsBaseChangePi
public import SerrePositivity.CommutativeAlgebra.PerfectoidizationAlgebraMap
public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation

/-! # 有限自由加群との比較写像と錐の同種

## 概要

主開集合 `D(g)` の上の局所的な同型 `L ⊗ A ≃ L^r` から、分母を払って有限自由加群への写像 `A → R^r` を作り、その錐が `g` の冪で零になることを示す（`exists_finiteFree_comparison_of_tensor_equiv`）。階数の像の有限直積 `R → ∏ R_n`（CommutativeAlgebra/RankLocus）の錐の冪による零化（`rankImageProduct_cone_isogeny`）と、局所分裂の共通対象での可換図式（`exists_common_square_of_localized_splitting`、その perfectoid 化の版）も与える。

## 方針

有限表示性で局所同型の分母を払い、`finiteFreeConeIsogeny`（HomologicalAlgebra/ScalarConeAnnihilators）へ渡す。共通対象から局所化への写像は単射でなくてよい。

## 規約

旧 `CLMST/Prop247RankCone`・`Prop247FiniteFreeComparison`・`Prop247CommonSquare`（CLMST Prop 2.4.7 の証明の比較写像の段）。宣言名の接頭辞 `prop247_` を外した。

## 使われ方

CLMST の `PerfectoidizationIsogeny`（Prop 2.4.7）の局所比較と階数による帰着。
-/

@[expose] public noncomputable section

universe u

section RankConePart

namespace SerrePositivity
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- 通常の元の rank 像への直積写像の実錐は g の一つの冪で零化される。
核の有限生成性、各 Ri の有限表示性は仮定しない。 -/
theorem rankImageProduct_cone_isogeny
    (R S : Type u) [CommRing R] [IsReduced R] [CommRing S] [Algebra R S]
    [Module.Finite R S] (g : R)
    (hetale : letI := GenericEtale.awayAlgebra R S g
      Algebra.Etale (Localization.Away g) (Localization.Away (algebraMap R S g)))
    (t : Finset ℕ)
    (ht : ∀ x : PrimeSpectrum.basicOpen g, awayRank R S g x ∈ t) :
    ∃ q : ℕ, moduleMapConeScalar R
      (toRankImageProduct R S g hetale t).toLinearMap (g ^ q) = 0 := by
  let P := rankImageProduct R S g hetale t
  let f := toRankImageProduct R S g hetale t
  letI : Module.Finite R P := rankImageProduct_finite R S g hetale t
  have hloc := toRankImageProduct_away_bijective R S g hetale t ht
  have hk (x : R) (hx : f x = 0) : g • x = 0 := by
    obtain ⟨n, hn⟩ := Localization.awayMap_injective_iff.mp hloc.1 x hx
    exact mul_eq_zero_of_pow_mul_eq_zero g x ⟨n, hn⟩
  have hc : ∃ n : ℕ, ∀ y : P ⧸ f.toLinearMap.range, g ^ n • y = 0 := by
    apply exists_uniform_pow_smul_zero g
    intro y
    obtain ⟨y, rfl⟩ := f.toLinearMap.range.mkQ_surjective y
    obtain ⟨r, n, hr⟩ := Localization.awayMap_surjective_iff.mp hloc.2 y
    refine ⟨n, ?_⟩
    rw [← map_smul]
    apply (Submodule.Quotient.mk_eq_zero f.toLinearMap.range).mpr
    refine ⟨r, ?_⟩
    rw [Algebra.smul_def, map_pow]
    exact hr
  obtain ⟨n, hn⟩ := hc
  refine ⟨1 + n, ?_⟩
  rw [pow_add, pow_one]
  exact moduleMapConeScalar_eq_zero_of_ker_coker_annihilated R f.toLinearMap g (g ^ n) hk hn

end SerrePositivity

end RankConePart

section FiniteFreeComparisonPart

namespace SerrePositivity
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R M : Type u} [CommRing R] [IsReduced R]
    [AddCommGroup M] [Module R M] [Module.FinitePresentation R M]

/-- 元の局所自由同型の一つの分母を払い、その同型を保つ実写像と錐零化を得る。
rank 0・零環・g の零因子性を排除しない。 -/
theorem exists_finiteFree_comparison_of_tensor_equiv
    (g : R) (A : Type u) [CommRing A] [Algebra R A] [IsLocalization (.powers g) A]
    (r : ℕ) (e : A ⊗[R] M ≃ₗ[A] (Fin r → A)) :
    ∃ (k : ℕ) (u : M →ₗ[R] (Fin r → R)),
      (∀ x : M, ∀ i : Fin r, algebraMap R A (u x i) =
        (algebraMap R A g) ^ k * e (1 ⊗ₜ[R] x) i) ∧
      Function.Bijective (awayModuleMap g u) ∧
      ∃ q : ℕ, moduleMapConeScalar R u (g ^ q) = 0 ∧
        (∀ x : u.ker, g ^ q • x = 0) ∧
        (∀ y : (Fin r → R) ⧸ u.range, g ^ q • y = 0) := by
  let S := Submonoid.powers g
  let ιM := LocalizedModule.mkLinearMap S M
  let ιF := LocalizedModule.mkLinearMap S (Fin r → R)
  let j : (Fin r → R) →ₗ[R] (Fin r → A) :=
    LinearMap.pi (fun i => (Algebra.linearMap R A).comp (LinearMap.proj i))
  have : IsLocalizedModule S j := IsLocalizedModule.pi S (fun _ : Fin r => Algebra.linearMap R A)
  let eF := IsLocalizedModule.linearEquiv S ιF j
  let jM := TensorProduct.mk R A M (1 : A)
  have : IsLocalizedModule S jM := IsLocalization.tensorProduct_isLocalizedModule S A
  let eM := IsLocalizedModule.linearEquiv S ιM jM
  let e' := eM.trans ((e.restrictScalars R).trans eF.symm)
  obtain ⟨k, u, hu, hbij⟩ := exists_away_comparison_of_finitePresentation g e'
  refine ⟨k, u, ?_, hbij, finiteFreeConeIsogeny_with_annihilators R g r u hbij⟩
  intro x i
  have hx := LinearMap.congr_fun hu (ιM x)
  change awayModuleMap g u (ιM x) = g ^ k • e' (ιM x) at hx
  rw [awayModuleMap, IsLocalizedModule.map_apply] at hx
  have hh := congrArg (fun z => eF z) hx
  have hm : eM (ιM x) = (1 : A) ⊗ₜ[R] x :=
    IsLocalizedModule.linearEquiv_apply S ιM jM x
  have hz : j (u x) = g ^ k • e (1 ⊗ₜ[R] x) := by
    change eF (ιF (u x)) = eF ((g ^ k : R) • e' (ιM x)) at hh
    rw [show eF (ιF (u x)) = j (u x) from
      IsLocalizedModule.linearEquiv_apply S ιF j (u x), map_smul] at hh
    calc
      j (u x) = g ^ k • eF (e' (ιM x)) := hh
      _ = g ^ k • eF (eF.symm (e (eM (ιM x)))) := rfl
      _ = g ^ k • e (eM (ιM x)) :=
        congrArg (fun z => (g ^ k : R) • z) (eF.apply_symm_apply _)
      _ = g ^ k • e (1 ⊗ₜ[R] x) := by rw [hm]
  have hi := congrFun hz i
  change algebraMap R A (u x i) = (g ^ k : R) • e (1 ⊗ₜ[R] x) i at hi
  simpa only [Algebra.smul_def, map_pow] using hi

end SerrePositivity

end FiniteFreeComparisonPart

section CommonSquarePart

namespace SerrePositivity
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- 元の共通対象への二つの写像と局所分裂から、共通対象内で厳密に可換な
有限自由比較を作る。almost 比較や perfectoid 化の引用を要求しない。 -/
theorem exists_common_square_of_localized_splitting
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
    exists_finiteFree_comparison_of_tensor_equiv d L r e
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
theorem exists_perfectoid_common_square
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
    exists_common_square_of_localized_splitting d L r e.toLinearEquiv
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

end SerrePositivity

end CommonSquarePart
