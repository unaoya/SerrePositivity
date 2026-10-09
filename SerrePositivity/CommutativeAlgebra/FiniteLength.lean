module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.RingTheory.FiniteLength
public import Mathlib.RingTheory.HopkinsLevitzki
public import Mathlib.RingTheory.KrullDimension.Zero
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.LocalRing.Quotient
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.RingTheory.SimpleModule.Basic
public import Mathlib.Algebra.Module.Torsion.Basic

/-!
# 有限長加群

Noether 環上：`T ⧸ I` が Artin 環なら、`√(Ann M) ⊇ I` となる有限生成加群 `M` は有限長
（台つき完全複体のホモロジーが有限長であることに使う）。

局所環上（Lemma 3.4 の組成列による帰納法、`notes/lemma-3-4.md`）：

- 局所環上の単純加群は剰余体 `A ⧸ m` と同型。
- `N ≤ M` で `M ⧸ N` が単純なら `length M = length N + 1`。
- 有限長加群は `m` の冪で消える。
- `z` が `m` を生成すれば `A ⧸ (z)` は剰余体で、有限生成な非零加群はそこへ全射する。
-/

@[expose] public section

universe u

open CategoryTheory Limits IsLocalRing

namespace SerrePositivity

/-! ## Noether 環上 -/

section noetherian

variable {T : Type u} [CommRing T] [IsNoetherianRing T]

/-- `T ⧸ I` が Artin 環で `I ≤ √J` なら `T ⧸ J` も Artin 環。 -/
lemma isArtinianRing_quotient_of_le_radical (I J : Ideal T)
    [IsArtinianRing (T ⧸ I)] (hIJ : I ≤ J.radical) : IsArtinianRing (T ⧸ J) := by
  have : IsNoetherianRing (T ⧸ J) :=
    isNoetherianRing_of_surjective T _ (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  apply (isArtinianRing_iff_krullDimLE_zero).mpr
  apply Ideal.krullDimLE_zero_quotient_iff_forall_minimalPrimes_isMaximal.mpr
  intro p hp
  have : p.IsPrime := hp.1.1
  have hIp : I ≤ p := hIJ.trans ((Ideal.IsPrime.radical_le_iff ‹p.IsPrime›).mpr hp.1.2)
  have : (p.map (Ideal.Quotient.mk I)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by simpa using hIp)
  have : (p.map (Ideal.Quotient.mk I)).IsMaximal := Ideal.IsPrime.isMaximal' inferInstance
  have h := Ideal.comap_isMaximal_of_surjective (Ideal.Quotient.mk I)
    Ideal.Quotient.mk_surjective (K := p.map (Ideal.Quotient.mk I))
  simpa [Ideal.comap_map_of_surjective, sup_eq_right.mpr hIp] using h

/-- Artin 的な閉部分スキームに台をもつ有限生成加群は有限長。 -/
lemma isFiniteLength_of_le_radical_annihilator (I : Ideal T)
    [IsArtinianRing (T ⧸ I)] (M : Type u) [AddCommGroup M] [Module T M]
    [Module.Finite T M] (hI : I ≤ (Module.annihilator T M).radical) : IsFiniteLength T M := by
  have : IsArtinianRing (T ⧸ Module.annihilator T M) :=
    isArtinianRing_quotient_of_le_radical I _ hI
  let hM := Module.isTorsionBySet_annihilator T M
  let := hM.module
  let : RingHomSurjective (Ideal.Quotient.mk (Module.annihilator T M)) :=
    ⟨Ideal.Quotient.mk_surjective⟩
  have : IsNoetherian (T ⧸ Module.annihilator T M) M :=
    isNoetherian_of_surjective hM.semilinearMap
      (LinearMap.range_eq_top.mpr Function.surjective_id)
  have : IsArtinian (T ⧸ Module.annihilator T M) M := inferInstance
  have : IsArtinian T M :=
    (hM.semilinearMap.isArtinian_iff_of_bijective Function.bijective_id).mpr inferInstance
  exact isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩

end noetherian

/-! ## 局所環上 -/

variable {A : Type u} [CommRing A] [IsLocalRing A]
variable {M : Type u} [AddCommGroup M] [Module A M]

/-- 局所環上の単純加群は剰余体 `A ⧸ m` と同型。 -/
lemma IsSimpleModule.nonempty_linearEquiv_quotient_maximalIdeal [IsSimpleModule A M] :
    Nonempty (M ≃ₗ[A] A ⧸ maximalIdeal A) := by
  obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp ‹IsSimpleModule A M›
  exact ⟨e.trans (Submodule.quotEquivOfEq I (maximalIdeal A) (eq_maximalIdeal hI))⟩

omit [IsLocalRing A] in
/-- `N ≤ M` で `M ⧸ N` が単純なら `length M = length N + 1`。 -/
lemma Module.length_eq_succ_of_isSimpleModule_quotient (N : Submodule A M)
    [IsSimpleModule A (M ⧸ N)] : Module.length A M = Module.length A N + 1 := by
  rw [Module.length_eq_add_of_exact N.subtype N.mkQ N.injective_subtype N.mkQ_surjective
    (LinearMap.exact_subtype_mkQ N), Module.length_eq_one A (M ⧸ N)]

/-- 有限長加群は `m` の冪で消える。 -/
lemma IsFiniteLength.exists_isTorsionBySet_maximalIdeal_pow (h : IsFiniteLength A M) :
    ∃ n : ℕ, Module.IsTorsionBySet A M ((maximalIdeal A) ^ n : Ideal A) := by
  induction h with
  | of_subsingleton => exact ⟨0, fun x _ ↦ Subsingleton.elim _ _⟩
  | @of_simple_quotient M _ _ N _ _ ih =>
    obtain ⟨n, hn⟩ := ih
    refine ⟨n + 1, ?_⟩
    obtain ⟨e⟩ :=
      IsSimpleModule.nonempty_linearEquiv_quotient_maximalIdeal (A := A) (M := M ⧸ N)
    -- `m • M ⊆ N`：`M ⧸ N ≃ A ⧸ m` は `m` で消える
    have hmN : ∀ (c : A), c ∈ maximalIdeal A → ∀ x : M, c • x ∈ N := by
      intro c hc x
      rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_smul]
      apply e.injective
      rw [map_smul, map_zero]
      obtain ⟨y, hy⟩ :=
        Submodule.Quotient.mk_surjective (maximalIdeal A) (e (Submodule.Quotient.mk x))
      rw [← hy, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      exact Ideal.mul_mem_right y _ hc
    intro x a
    obtain ⟨a, ha⟩ := a
    change a • x = 0
    have ha' : a ∈ maximalIdeal A ^ n * maximalIdeal A := by rw [← pow_succ]; exact ha
    refine Submodule.mul_induction_on ha' (fun b hb c hc ↦ ?_) (fun u v hu hv ↦ ?_)
    · -- `(b * c) • x = b • (c • x)`、`c • x ∈ N`、`N` は `m ^ n` で消える
      rw [mul_smul]
      have := @hn ⟨c • x, hmN c hc x⟩ ⟨b, hb⟩
      rw [Subtype.ext_iff] at this
      simpa using this
    · rw [add_smul, hu, hv, add_zero]

/-! ## `m` を生成する列 -/

section span

variable {e : ℕ} {z : Fin e → A} (hz : Ideal.span (Set.range z) = maximalIdeal A)

include hz in
/-- `z` が `m` を生成すれば `A ⧸ (z)` は剰余体なので Artin 環。 -/
lemma isArtinianRing_quotient_span_of_eq : IsArtinianRing (A ⧸ Ideal.span (Set.range z)) := by
  rw [hz]
  exact inferInstanceAs (IsArtinianRing (ResidueField A))

include hz in
/-- `z` が `m` を生成すれば `A ⧸ (z)` は単純 `A` 加群。 -/
lemma isSimpleModule_quotient_span_of_eq : IsSimpleModule A (A ⧸ Ideal.span (Set.range z)) := by
  rw [hz, isSimpleModule_iff_isCoatom]
  exact Ideal.isMaximal_def.mp (maximalIdeal.isMaximal A)

include hz in
/-- 有限生成で `0` でない加群は `A/(z) = k` に全射をもつ。 -/
lemma exists_surjective_quotient_span (H : ModuleCat.{u} A) [Module.Finite A H]
    (hH : ¬ IsZero H) :
    ∃ ε : H ⟶ ModuleCat.of A (A ⧸ Ideal.span (Set.range z)), Function.Surjective ε.hom := by
  have : Nontrivial H := by
    rw [ModuleCat.isZero_iff_subsingleton] at hH
    exact not_subsingleton_iff_nontrivial.mp hH
  obtain h | ⟨N, hN, -⟩ := IsCoatomic.eq_top_or_exists_le_coatom (⊥ : Submodule A H)
  · exact absurd h bot_ne_top
  have : IsSimpleModule A (H ⧸ N) := isSimpleModule_iff_isCoatom.mpr hN
  obtain ⟨φ⟩ := IsSimpleModule.nonempty_linearEquiv_quotient_maximalIdeal (A := A) (M := H ⧸ N)
  let ψ := φ.trans (Submodule.quotEquivOfEq _ _ hz.symm)
  exact ⟨ModuleCat.ofHom (ψ.toLinearMap ∘ₗ N.mkQ), ψ.surjective.comp N.mkQ_surjective⟩

end span

end SerrePositivity
