module

public import SerrePositivity.BhattScholze.PerfectoidIdeal.Powers
public import SerrePositivity.BhattScholze.Semiperfectoid.CompatibleRootPerfectoid
public import SerrePositivity.CommutativeAlgebra.ScalarIsogeny

/-! # perfectoid イデアルと互換根のイデアル、被覆からの貼り合わせ

## 概要

選んだ主イデアル商の perfectoid 化を、互換根の完備化の商と元の普遍写像を通じて比べ、perfectoid イデアルが `p` の冪を法として互換根のイデアルに一致することを示す。根を持つ被覆の各成分で零化されれば元の perfectoid イデアルでも零化されること（被覆のイデアルに生成元の冪が入れば十分）、環の引き戻しの四角で左下の代数だけが perfectoid なら核・余核が perfectoid イデアルで零化されることを与える。
BS 著者版 Theorem 7.14 の被覆と §10.1 の perfectoid 核を、両立する根を用いる比較に使う。

## 方針

互換根の族の完備化が元のイデアルを検出し、`p` 冪の精度で評価すると局所的な perfectoid イデアルの和に戻ることを使う。

## 規約

整代数の perfectoid 化の存在の引用は使わない。特定の修正の excision の四角は主張しない。旧 `CommutativeAlgebra/PerfectoidIdealCompatibleRoots`・`PerfectoidIdealCover`・`PerfectoidIdealPullback`。

## 使われ方

CLMST の KL 比較と Prop 2.4.7。
-/

@[expose] public noncomputable section

universe u

section PerfectoidIdealCompatibleRootsPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open BhattScholze
variable (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime]
    (hR : IsIntegralPerfectoid R p) (ρ : ℕ → R)
    (hρ : ∀ n, ρ (n + 1) ^ p = ρ n)
include hρ

/-- The actual B3 kernel is the kernel of the actual completed root-ideal quotient map. -/
theorem perfectoidIdeal_eq_compatibleRootCompletion_kernel :
    perfectoidIdeal R p hR (ρ 0) = RingHom.ker
      ((algebraMap (R ⧸ SerrePositivity.compatibleRootIdeal ρ) (CompatibleRootCompletion p ρ)).comp
        (Ideal.Quotient.mk (SerrePositivity.compatibleRootIdeal ρ))) := by
  let : Algebra.FinitePresentation R (R ⧸ Ideal.span {ρ 0}) :=
    Algebra.FinitePresentation.quotient (Submodule.fg_span_singleton (ρ 0))
  have hf := isPerfectoidization_toQuotientPerfectoidization R (Ideal.span {ρ 0}) p hR
  have hg := compatibleRootCompletionMap_isPerfectoidization hR ρ hρ
  have he := IsPerfectoidization.ker_comp_eq p hf hg (Ideal.Quotient.mk (Ideal.span {ρ 0}))
  have hc : (compatibleRootCompletionMap p ρ).comp (Ideal.Quotient.mk (Ideal.span {ρ 0})) =
      (algebraMap (R ⧸ SerrePositivity.compatibleRootIdeal ρ) (CompatibleRootCompletion p ρ)).comp
        (Ideal.Quotient.mk (SerrePositivity.compatibleRootIdeal ρ)) := by
    ext x
    rfl
  rw [hc] at he
  exact he

/-- At every p-power precision, elements of the perfectoid ideal lie in the root ideal. -/
theorem perfectoidIdeal_le_compatibleRootIdeal_sup_p_pow (k : ℕ) :
    perfectoidIdeal R p hR (ρ 0) ≤ SerrePositivity.compatibleRootIdeal ρ ⊔
      Ideal.span {(p : R) ^ k} := by
  let J := SerrePositivity.compatibleRootIdeal ρ
  let Q := R ⧸ J
  let q : R →+* Q := Ideal.Quotient.mk J
  let P : Ideal Q := Ideal.span {(p : Q)}
  let K : Ideal R := Ideal.span {(p : R) ^ k}
  intro x hx
  rw [perfectoidIdeal_eq_compatibleRootCompletion_kernel R p hR ρ hρ] at hx
  change algebraMap Q (CompatibleRootCompletion p ρ) (q x) = 0 at hx
  have hy := congrArg (AdicCompletion.evalₐ P k) hx
  simp only [AdicCompletion.algebraMap_apply, map_zero] at hy
  have hmem : q x ∈ P ^ k := Ideal.Quotient.eq_zero_iff_mem.mp hy
  have hmap : K.map q = P ^ k := by
    simp only [K, P, Ideal.map_span, Set.image_singleton, map_pow, map_natCast,
      Ideal.span_singleton_pow]
  have hxmap : x ∈ (K.map q).comap q := by
    change q x ∈ K.map q
    rw [hmap]
    exact hmem
  have hcomap : (K.map q).comap q = K ⊔ J := by
    rw [Ideal.comap_map_of_surjective q Ideal.Quotient.mk_surjective,
      ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
  rw [hcomap] at hxmap
  exact (sup_comm K J ▸ hxmap)

/-- The roots themselves lie in the original B3 perfectoid ideal. -/
theorem compatibleRootIdeal_le_perfectoidIdeal :
    SerrePositivity.compatibleRootIdeal ρ ≤ perfectoidIdeal R p hR (ρ 0) := by
  rw [perfectoidIdeal_eq_compatibleRootCompletion_kernel R p hR ρ hρ]
  intro x hx
  change algebraMap (R ⧸ SerrePositivity.compatibleRootIdeal ρ)
    (CompatibleRootCompletion p ρ) (Ideal.Quotient.mk _ x) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero]

/-- The ideal and the explicit root ideal agree to every p-power precision. -/
theorem perfectoidIdeal_sup_p_pow_eq_compatibleRootIdeal (k : ℕ) :
    perfectoidIdeal R p hR (ρ 0) ⊔ Ideal.span {(p : R) ^ k} =
      SerrePositivity.compatibleRootIdeal ρ ⊔ Ideal.span {(p : R) ^ k} := by
  apply le_antisymm
  · exact sup_le (perfectoidIdeal_le_compatibleRootIdeal_sup_p_pow R p hR ρ hρ k) le_sup_right
  · exact sup_le_sup (compatibleRootIdeal_le_perfectoidIdeal R p hR ρ hρ) le_rfl

/-- The images in the actual R/p^k quotient agree, including k = 0. -/
theorem perfectoidIdeal_mod_p_pow_eq_compatibleRootIdeal (k : ℕ) :
    (perfectoidIdeal R p hR (ρ 0)).map (Ideal.Quotient.mk (Ideal.span {(p : R) ^ k})) =
      (SerrePositivity.compatibleRootIdeal ρ).map
        (Ideal.Quotient.mk (Ideal.span {(p : R) ^ k})) := by
  apply (Ideal.map_eq_iff_sup_ker_eq_of_surjective
    (Ideal.Quotient.mk (Ideal.span {(p : R) ^ k})) Ideal.Quotient.mk_surjective).mpr
  rw [Ideal.mk_ker]
  exact perfectoidIdeal_sup_p_pow_eq_compatibleRootIdeal R p hR ρ hρ k

/-- Any ideal containing p^k contains the perfectoid ideal exactly when it contains every root. -/
theorem perfectoidIdeal_le_iff_compatible_roots (J : Ideal R) (k : ℕ)
    (hp : (p : R) ^ k ∈ J) :
    perfectoidIdeal R p hR (ρ 0) ≤ J ↔ ∀ n, ρ n ∈ J := by
  constructor
  · intro h n
    exact h ((compatibleRootIdeal_le_perfectoidIdeal R p hR ρ hρ)
      (Ideal.mem_span_range_self (x := n)))
  · intro h
    apply (perfectoidIdeal_le_compatibleRootIdeal_sup_p_pow R p hR ρ hρ k).trans
    apply sup_le
    · apply Ideal.span_le.mpr
      rintro _ ⟨n, rfl⟩
      exact h n
    · exact (Ideal.span_singleton_le_iff_mem J).mpr hp

/-- A p-adically separated ideal quotient detects containment of the perfectoid
ideal through the original compatible roots. -/
theorem perfectoidIdeal_le_iff_compatible_roots_of_quotient_isHausdorff
    (J : Ideal R) [IsHausdorff (Ideal.span {(p : R ⧸ J)}) (R ⧸ J)] :
    perfectoidIdeal R p hR (ρ 0) ≤ J ↔ ∀ n, ρ n ∈ J := by
  constructor
  · intro h n
    exact h ((compatibleRootIdeal_le_perfectoidIdeal R p hR ρ hρ)
      (Ideal.mem_span_range_self (x := n)))
  · intro h s hs
    let Q := R ⧸ J
    let q : R →+* Q := Ideal.Quotient.mk J
    have hroot : SerrePositivity.compatibleRootIdeal ρ ≤ J := by
      apply Ideal.span_le.mpr
      rintro _ ⟨n, rfl⟩
      exact h n
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    apply IsHausdorff.haus
      (inferInstance : IsHausdorff (Ideal.span {(p : Q)}) Q) (q s)
    intro k
    obtain ⟨y, hy, z, hz, hsum⟩ := Submodule.mem_sup.mp
      (perfectoidIdeal_le_compatibleRootIdeal_sup_p_pow R p hR ρ hρ k hs)
    have hqy : q y = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (hroot hy)
    have hqz : q z ∈ (Ideal.span {(p : Q)}) ^ k := by
      have hm := Ideal.mem_map_of_mem q hz
      simpa only [Ideal.map_span, Set.image_singleton, map_pow, map_natCast,
        Ideal.span_singleton_pow] using hm
    have he : q s = q z := by rw [← hsum, map_add, hqy, zero_add]
    apply SModEq.zero.mpr
    change q s ∈ (Ideal.span {(p : Q)}) ^ k • (⊤ : Ideal Q)
    rw [Ideal.smul_eq_mul, Ideal.mul_top, he]
    exact hqz

/-- On an arbitrary p-power torsion module, almost zero is detected by
the action of each compatible root. -/
theorem perfectoidIdeal_annihilates_iff_compatible_roots
    (M : Type u) [AddCommGroup M] [Module R M] (k : ℕ)
    (hM : ∀ x : M, (p : R) ^ k • x = 0) :
    (∀ s ∈ perfectoidIdeal R p hR (ρ 0), ∀ x : M, s • x = 0) ↔
      ∀ n, ∀ x : M, ρ n • x = 0 := by
  constructor
  · intro h n x
    exact h _ ((compatibleRootIdeal_le_perfectoidIdeal R p hR ρ hρ)
      (Ideal.mem_span_range_self (x := n))) x
  · intro h s hs x
    have hroots : ∀ n, ρ n ∈ Module.annihilator R M :=
      fun n => Module.mem_annihilator.mpr (h n)
    have hI := (perfectoidIdeal_le_iff_compatible_roots R p hR ρ hρ
      (Module.annihilator R M) k (Module.mem_annihilator.mpr hM)).mpr hroots
    exact Module.mem_annihilator.mp (hI hs) x

end SerrePositivity

end PerfectoidIdealCompatibleRootsPart

section PerfectoidIdealCoverPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open BhattScholze
variable (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime]
    (hR : IsIntegralPerfectoid R p)

/-- Any map to a perfectoid ring killing g kills the original perfectoid ideal. -/
theorem perfectoidIdeal_le_ker_of_eq_zero {T : Type u} [CommRing T]
    (hT : IsIntegralPerfectoid T p) (f : R →+* T) (g : R) (hg : f g = 0) :
    perfectoidIdeal R p hR g ≤ RingHom.ker f := by
  let k : R ⧸ Ideal.span {g} →+* T := Ideal.Quotient.lift _ f
    (fun a ha => ((Ideal.span_singleton_le_iff_mem (RingHom.ker f)).mpr hg) ha)
  obtain ⟨l, hl, _⟩ :=
    (isPerfectoidization_toQuotientPerfectoidization R (Ideal.span {g}) p hR).2 T hT k
  intro x hx
  change toQuotientPerfectoidization R (Ideal.span {g}) p hR
    (Ideal.Quotient.mk _ x) = 0 at hx
  have he := RingHom.congr_fun hl (Ideal.Quotient.mk (Ideal.span {g}) x)
  change l (toQuotientPerfectoidization R (Ideal.span {g}) p hR
    (Ideal.Quotient.mk _ x)) = f x at he
  rw [hx, map_zero] at he
  exact he.symm

/-- A rooted cover controls the original ideal to every p-power precision. -/
theorem perfectoidIdeal_le_compatibleRootFamilyIdeal_sup_p_pow
    {σ : Type u} (ρ : σ → ℕ → R) (hρ : ∀ s n, ρ s (n + 1) ^ p = ρ s n)
    (g : R) (N : ℕ) (hcover : g ^ N ∈ compatibleRootFamilyZeroIdeal ρ) (k : ℕ) :
    perfectoidIdeal R p hR g ≤ compatibleRootFamilyIdeal ρ ⊔ Ideal.span {(p : R) ^ k} := by
  let J := compatibleRootFamilyIdeal ρ
  let Q := R ⧸ J
  let q : R →+* Q := Ideal.Quotient.mk J
  let P := CompatibleRootFamilyCompletion p ρ
  let κ : R →+* P := (algebraMap Q P).comp q
  have hP : IsIntegralPerfectoid P p := compatibleRootFamilyCompletion_isIntegralPerfectoid hR ρ hρ
  let := hP.isReduced P p
  have hg : κ g = 0 := by
    apply IsReduced.eq_zero
    refine ⟨N, ?_⟩
    rw [← map_pow]
    change algebraMap Q P (q (g ^ N)) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr (compatibleRootFamilyZeroIdeal_le ρ hcover), map_zero]
  have hI := perfectoidIdeal_le_ker_of_eq_zero R p hR hP κ g hg
  intro x hx
  have hz := hI hx
  change algebraMap Q P (q x) = 0 at hz
  have hy := congrArg (AdicCompletion.evalₐ (Ideal.span {(p : Q)}) k) hz
  simp only [map_zero] at hy
  have hmem : q x ∈ (Ideal.span {(p : Q)}) ^ k := Ideal.Quotient.eq_zero_iff_mem.mp hy
  let K : Ideal R := Ideal.span {(p : R) ^ k}
  have hmap : K.map q = (Ideal.span {(p : Q)}) ^ k := by
    simp only [K, Ideal.map_span, Set.image_singleton, map_pow, map_natCast,
      Ideal.span_singleton_pow]
  have hxmap : x ∈ (K.map q).comap q := by
    change q x ∈ K.map q
    rw [hmap]
    exact hmem
  have hcomap : (K.map q).comap q = K ⊔ J := by
    rw [Ideal.comap_map_of_surjective q Ideal.Quotient.mk_surjective,
      ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
  rw [hcomap] at hxmap
  exact sup_comm K J ▸ hxmap

/-- The local perfectoid ideals generate the original one modulo each p power. -/
theorem perfectoidIdeal_le_iSup_sup_p_pow_of_rooted_cover
    {σ : Type u} (ρ : σ → ℕ → R) (hρ : ∀ s n, ρ s (n + 1) ^ p = ρ s n)
    (g : R) (N : ℕ) (hcover : g ^ N ∈ compatibleRootFamilyZeroIdeal ρ) (k : ℕ) :
    perfectoidIdeal R p hR g ≤ (⨆ s, perfectoidIdeal R p hR (ρ s 0)) ⊔
      Ideal.span {(p : R) ^ k} := by
  apply (perfectoidIdeal_le_compatibleRootFamilyIdeal_sup_p_pow R p hR ρ hρ g N hcover k).trans
  apply sup_le_sup _ le_rfl
  apply Ideal.span_le.mpr
  rintro _ ⟨⟨s, n⟩, rfl⟩
  exact (le_iSup (fun s => perfectoidIdeal R p hR (ρ s 0)) s)
    ((compatibleRootIdeal_le_perfectoidIdeal R p hR (ρ s) (hρ s))
      (Ideal.mem_span_range_self (x := n)))

/-- Local almost annihilation glues on arbitrary p-power-torsion modules.
The cover need not be finite and the test module need not be finitely generated. -/
theorem perfectoidIdeal_annihilates_of_rooted_cover
    {σ : Type u} (ρ : σ → ℕ → R) (hρ : ∀ s n, ρ s (n + 1) ^ p = ρ s n)
    (g : R) (N : ℕ) (hcover : g ^ N ∈ compatibleRootFamilyZeroIdeal ρ)
    (M : Type u) [AddCommGroup M] [Module R M] (k : ℕ)
    (hM : ∀ x : M, (p : R) ^ k • x = 0)
    (hlocal : ∀ s, ∀ a ∈ perfectoidIdeal R p hR (ρ s 0), ∀ x : M, a • x = 0) :
    ∀ a ∈ perfectoidIdeal R p hR g, ∀ x : M, a • x = 0 := by
  have hsum : (⨆ s, perfectoidIdeal R p hR (ρ s 0)) ≤ Module.annihilator R M :=
    iSup_le (fun s a ha => Module.mem_annihilator.mpr (hlocal s a ha))
  have hp : Ideal.span {(p : R) ^ k} ≤ Module.annihilator R M :=
    (Ideal.span_singleton_le_iff_mem _).mpr (Module.mem_annihilator.mpr hM)
  have hI := (perfectoidIdeal_le_iSup_sup_p_pow_of_rooted_cover R p hR ρ hρ g N hcover k).trans
    (sup_le hsum hp)
  exact fun a ha => Module.mem_annihilator.mp (hI ha)

end SerrePositivity

end PerfectoidIdealCoverPart

section PerfectoidIdealPullbackPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits

/-- An actual ring pullback with a perfectoid closed-side algebra gives almost
annihilation of the top map over the original perfectoid base. -/
theorem perfectoidIdeal_ker_coker_annihilated_of_isPullback
    {R A B C D : Type u} [CommRing R] [CommRing A] [CommRing B]
    [CommRing C] [CommRing D] [Algebra R A] [Algebra R B] [Algebra R C] [Algebra R D]
    {p : ℕ} [Fact p.Prime] (hR : IsIntegralPerfectoid R p)
    (f : A →ₐ[R] B) (l : A →ₐ[R] C) (r : B →ₐ[R] D) (b : C →ₐ[R] D)
    (hPB : IsPullback (CommRingCat.ofHom f.toRingHom) (CommRingCat.ofHom l.toRingHom)
      (CommRingCat.ofHom r.toRingHom) (CommRingCat.ofHom b.toRingHom))
    (hC : IsIntegralPerfectoid C p) (g : R) (hg : algebraMap R C g = 0) :
    (∀ s ∈ perfectoidIdeal R p hR g, ∀ x : f.toLinearMap.ker, s • x = 0) ∧
    (∀ s ∈ perfectoidIdeal R p hR g, ∀ y : B ⧸ f.toLinearMap.range, s • y = 0) := by
  have hI := perfectoidIdeal_le_ker_of_eq_zero R p hR hC (algebraMap R C) g hg
  exact ⟨fun s hs => (algHom_ker_coker_annihilated_of_isPullback f l r b hPB s (hI hs)).1,
    fun s hs => (algHom_ker_coker_annihilated_of_isPullback f l r b hPB s (hI hs)).2⟩

/-- The actual projection from the concrete fiber product is an almost
comparison when its closed-side factor is perfectoid and kills the generator. -/
theorem perfectoidIdeal_ker_coker_annihilated_pullbackFst
    {R B C D : Type u} [CommRing R] [CommRing B] [CommRing C] [CommRing D]
    [Algebra R B] [Algebra R C] [Algebra R D]
    {p : ℕ} [Fact p.Prime] (hR : IsIntegralPerfectoid R p)
    (r : B →ₐ[R] D) (b : C →ₐ[R] D)
    (hC : IsIntegralPerfectoid C p) (g : R) (hg : algebraMap R C g = 0) :
    (∀ s ∈ perfectoidIdeal R p hR g,
      ∀ x : (AlgHom.pullbackFst r b).toLinearMap.ker, s • x = 0) ∧
    (∀ s ∈ perfectoidIdeal R p hR g,
      ∀ y : B ⧸ (AlgHom.pullbackFst r b).toLinearMap.range, s • y = 0) :=
  perfectoidIdeal_ker_coker_annihilated_of_isPullback hR
    (AlgHom.pullbackFst r b) (AlgHom.pullbackSnd r b) r b
    (algHom_isPullback_pullback r b) hC g hg

end SerrePositivity

end PerfectoidIdealPullbackPart
