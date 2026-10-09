module

public import SerrePositivity.CommutativeAlgebra.FiniteLength
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# 剰余体が同じときの長さの比較

`A → T` で `T` が局所環、`A → T → T/m_T` が全射（剰余体が同じ）なら、`T` 加群の `A` 上の長さと
`T` 上の長さは一致する。単純 `T` 加群は `A` 上でも単純であることによる。
-/

@[expose] public section

universe u

open CategoryTheory IsLocalRing

namespace SerrePositivity

section length

variable {A T : Type u} [CommRing A] [CommRing T] [Algebra A T] [IsLocalRing T]
  (hres : Function.Surjective ((residue T).comp (algebraMap A T)))

include hres in
/-- 剰余体が同じなら、単純 `T` 加群は `A` 上でも単純。 -/
lemma isSimpleModule_of_residue_surjective (S : Type u) [AddCommGroup S] [Module T S]
    [Module A S] [IsScalarTower A T S] [IsSimpleModule T S] : IsSimpleModule A S := by
  obtain ⟨φ⟩ := IsSimpleModule.nonempty_linearEquiv_quotient_maximalIdeal (A := T) (M := S)
  -- `m_T` は `S` を消す
  have hkill : ∀ t ∈ maximalIdeal T, ∀ x : S, t • x = 0 := by
    intro t ht x
    apply φ.injective
    rw [map_smul, map_zero]
    obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (φ x)
    rw [← hy, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, smul_eq_mul]
    exact Ideal.mul_mem_right _ _ ht
  -- `A` 部分加群は `T` 部分加群
  have hT : ∀ (p : Submodule A S) (t : T) (x : S), x ∈ p → t • x ∈ p := by
    intro p t x hx
    obtain ⟨a, ha⟩ := hres (residue T t)
    have hm : t - algebraMap A T a ∈ maximalIdeal T := by
      rw [← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero]
      exact ha.symm
    have : t • x = a • x := by
      rw [← sub_eq_zero, ← algebraMap_smul T a x, ← sub_smul]
      exact hkill _ hm x
    rw [this]
    exact p.smul_mem a hx
  have : Nontrivial S := IsSimpleModule.nontrivial T S
  refine { eq_bot_or_eq_top := fun p ↦ ?_ }
  let q : Submodule T S :=
    { carrier := p
      add_mem' := p.add_mem
      zero_mem' := p.zero_mem
      smul_mem' := fun t x hx ↦ hT p t x hx }
  rcases IsSimpleOrder.eq_bot_or_eq_top q with h | h
  · left
    ext x
    have := SetLike.ext_iff.mp h x
    simpa [q] using this
  · right
    ext x
    have := SetLike.ext_iff.mp h x
    simpa [q] using this

include hres in
/-- 剰余体が同じ局所環 `T` 上では、`T` 加群の `A` 上の長さと `T` 上の長さは一致する。 -/
theorem length_eq_of_common_residueField (M : Type u) [AddCommGroup M] [Module T M]
    [Module A M] [IsScalarTower A T M] : Module.length A M = Module.length T M := by
  by_cases h : IsFiniteLength T M
  · suffices H : ∀ (M : Type u) [AddCommGroup M] [Module T M], IsFiniteLength T M →
        ∀ [Module A M] [IsScalarTower A T M], Module.length A M = Module.length T M from
      H M h
    intro M _ _ h
    induction h with
    | of_subsingleton => intro _ _; simp [Module.length_eq_zero]
    | @of_simple_quotient M _ _ N _ _ ih =>
      intro _ _
      have := isSimpleModule_of_residue_surjective hres (M ⧸ N)
      rw [Module.length_eq_succ_of_isSimpleModule_quotient N,
        Module.length_eq_add_of_exact (N.subtype.restrictScalars A) (N.mkQ.restrictScalars A)
          N.injective_subtype N.mkQ_surjective (LinearMap.exact_subtype_mkQ N),
        Module.length_eq_one A (M ⧸ N), ih]
  · have hT : Module.length T M = ⊤ := by
      by_contra hne
      exact h (Module.length_ne_top_iff.mp hne)
    rw [hT]
    by_contra hne
    have hA := Module.length_ne_top_iff.mp hne
    rw [isFiniteLength_iff_isNoetherian_isArtinian] at hA
    obtain ⟨_, _⟩ := hA
    have : IsNoetherian T M := isNoetherian_of_tower A inferInstance
    have : IsArtinian T M := isArtinian_of_tower A inferInstance
    exact h (isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩)

include hres in
/-- 係数制限した `T` 加群の `A` 上の長さは `T` 上の長さに等しい。 -/
lemma length_restrictScalars_eq (M : ModuleCat.{u} T) :
    Module.length A ((ModuleCat.restrictScalars (algebraMap A T)).obj M) =
      Module.length T M := by
  let : Module A M := Module.compHom M (algebraMap A T)
  have : IsScalarTower A T M := ⟨fun a t m ↦ by
    rw [Algebra.smul_def, mul_smul]
    rfl⟩
  exact length_eq_of_common_residueField hres M

end length

/-! ## 係数制限と長さ -/

section restrictScalars

variable {A T : Type u} [CommRing A] [CommRing T] [Algebra A T]

/-- 係数制限して有限長なら、もとの環の上でも有限長（部分加群の束が埋め込まれる）。 -/
lemma finiteLength_of_restrictScalars (M : ModuleCat.{u} T)
    (hM : IsFiniteLength A ((ModuleCat.restrictScalars (algebraMap A T)).obj M)) :
    IsFiniteLength T M := by
  let : Module A M := Module.compHom M (algebraMap A T)
  have : IsScalarTower A T M := IsScalarTower.of_algebraMap_smul (fun _ _ ↦ rfl)
  have h : IsFiniteLength A M := hM
  obtain ⟨hn, ha⟩ := isFiniteLength_iff_isNoetherian_isArtinian.mp h
  exact isFiniteLength_iff_isNoetherian_isArtinian.mpr
    ⟨isNoetherian_of_tower A hn, isArtinian_of_tower A ha⟩

end restrictScalars

section semilinear

variable {R S : Type u} [CommRing R] [CommRing S]

/-- 全射な環準同型の上の半線形全単射は長さを保つ（部分加群の束の同型による）。 -/
lemma length_eq_of_semilinear_bijective (φ : R →+* S) (hφ : Function.Surjective φ)
    {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N]
    (f : M →ₛₗ[φ] N) (hf : Function.Bijective f) : Module.length R M = Module.length S N := by
  have : RingHomSurjective φ := ⟨hφ⟩
  rw [Module.length, Module.length, WithBot.unbot_inj,
    Order.krullDim_eq_of_orderIso (Submodule.orderIsoMapComapOfBijective f hf)]

/-- 環自己同型に沿った係数制限は長さを保つ。 -/
lemma length_restrictScalars_equiv (σ : R ≃+* R) (M : ModuleCat.{u} R) :
    Module.length R ((ModuleCat.restrictScalars σ.toRingHom).obj M) = Module.length R M := by
  let f : (ModuleCat.restrictScalars σ.toRingHom).obj M →ₛₗ[σ.toRingHom] M :=
    { toFun := id, map_add' := fun _ _ ↦ rfl, map_smul' := fun _ _ ↦ rfl }
  exact length_eq_of_semilinear_bijective σ.toRingHom σ.surjective f Function.bijective_id

end semilinear

end SerrePositivity
