module

public import SerrePositivity.CommutativeAlgebra.Length.Basic
public import Mathlib.RingTheory.KrullDimension.Module
public import Mathlib.LinearAlgebra.Dimension.Torsion.Finite
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-! # 剰余体が同じ局所拡大の長さ

## 概要

環準同型 `A → T`（`T` は局所環）で合成 `A → T → T/m_T` が全射（剰余体が同じ）なら、`T` 加群の `A` 上の
長さと `T` 上の長さは一致する（`length_eq_of_common_residueField`）。あわせて、剰余体の同型
（`residueFieldEquiv_of_surjective`）、局所環 `R` 上有限な局所環 `T` で `m_T` の冪が `m_R T` に入ること
（`maximalIdeal_pow_le_map_of_finite`）、有限な局所拡大での極大イデアルの根基と剰余体の比較を集める。

## 方針

単純 `T` 加群は `T/m_T` と同型で、`T` の元は `A` の元と `m_T` の元の和に書けるので `A` 上でも単純。
冪の包含は `T/m_R T` が Artin 局所環であることによる。

## 規約

`A` の局所性は仮定しない（剰余体の全射性だけを使う）。

## 使われ方

論文 Lemma 3.4・3.5・5.2 と §2・§5、正規化長さの定義域の取り替え（`PerfectComplex/NormalizedLength`）、
交点重複度、パラメータ系の有限な拡大（`SystemOfParameters/Finite`）。
-/

@[expose] public noncomputable section

universe u v w

section LengthComparison

open CategoryTheory IsLocalRing

namespace SerrePositivity

section length

variable {A T : Type u} [CommRing A] [CommRing T] [Algebra A T] [IsLocalRing T]
  (hres : Function.Surjective ((residue T).comp (algebraMap A T)))

include hres in
/-- 剰余体が同じ（`A → T → T/m_T` が全射）なら、単純 `T` 加群 `S` は `A` 加群としても単純である。
単純 `T` 加群は `T ⧸ m_T` と同型なので `m_T` は `S` を消す。任意の `t ∈ T` は、剰余体への全射性から
`a ∈ A` の像と `m_T` の元の和に書けるので、`S` 上で `t` 倍は `a` 倍に等しい。したがって `S` の
`A` 部分加群は自動的に `T` 部分加群であり、`T` 上の単純性（部分加群は `⊥` か `⊤`）から `A` 上の
単純性が従う。 -/
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
/-- 剰余体が同じ局所環 `T` 上では、`T` 加群 `M` の `A` 上の長さと `T` 上の長さは一致する。
`M` が `T` 上有限長なら組成列についての帰納法：単純な商 `M ⧸ N` は `A` 上でも単純
（`isSimpleModule_of_residue_surjective`）なので、どちらの長さも一段で `1` ずつ増える。
`T` 上無限長なら `A` 上も無限長：`A` 上有限長なら Noether かつ Artin で、それは `T` 上の Noether 性・
Artin 性を含意する（`isNoetherian_of_tower`、`isArtinian_of_tower`）から。 -/
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
/-- `length_eq_of_common_residueField` を、`ModuleCat` の係数制限関手 `restrictScalars` の言葉で
述べたもの：係数制限した `T` 加群の `A` 上の長さは `T` 上の長さに等しい。複体の各項が `ModuleCat`
の対象として現れる場面（`Paper/Lemma3_5/Ordinary.lean`、Lemma 5.2）で使う形。 -/
lemma length_restrictScalars_eq (M : ModuleCat.{u} T) :
    Module.length A ((ModuleCat.restrictScalars (algebraMap A T)).obj M) =
      Module.length T M := by
  let : Module A M := Module.compHom M (algebraMap A T)
  have : IsScalarTower A T M := ⟨fun a t m ↦ by
    rw [Algebra.smul_def, mul_smul]
    rfl⟩
  exact length_eq_of_common_residueField hres M

end length

end SerrePositivity

end LengthComparison

section LocalExtension

open IsLocalRing

namespace SerrePositivity

variable {R : Type u} [CommRing R]

/-- 剰余体への射 `f : R → T → T/m_T` が全射なら、剰余体の同型 `R/m_R ≃+* T/m_T` が得られる。
`f` の核は（`T/m_T` が体なので）極大イデアルで、局所環の極大イデアルは `m_R` だけだから
`ker f = m_R`。あとは準同型定理 `R / ker f ≃ T/m_T`。 -/
noncomputable def residueFieldEquiv_of_surjective [IsLocalRing R]
    (T : Type u) [CommRing T] [IsLocalRing T] [Algebra R T]
    (hres : Function.Surjective ((residue T).comp (algebraMap R T))) :
    ResidueField R ≃+* ResidueField T := by
  let f := (residue T).comp (algebraMap R T)
  have : (RingHom.ker f).IsMaximal :=
    Ideal.comap_isMaximal_of_surjective f hres (K := ⊥)
  have hk : RingHom.ker f = maximalIdeal R := IsLocalRing.eq_maximalIdeal inferInstance
  exact (Ideal.quotEquivOfEq hk.symm).trans (RingHom.quotientKerEquivOfSurjective hres)

/-- 局所環 `R` 上有限な局所環 `T` では、`m_T` のある冪が `m_R T`（`m_R` の `T` への拡大）に入る。
`T ⧸ m_R T` は体 `R ⧸ m_R` 上の有限生成加群なので Artin 環であり、Artin 局所環では極大イデアルが
冪零である（Mathlib の `exists_maximalIdeal_pow_le_of_isArtinianRing_quotient`）。論文 Lemma 3.4 の
証明で使われる `m_T^N ⊆ m_A T` に当たる。 -/
theorem maximalIdeal_pow_le_map_of_finite [IsLocalRing R]
    (T : Type u) [CommRing T] [IsLocalRing T] [Algebra R T] [Module.Finite R T] :
    ∃ n : ℕ, (maximalIdeal T) ^ n ≤ (maximalIdeal R).map (algebraMap R T) := by
  let I := (maximalIdeal R).map (algebraMap R T)
  let : Field (R ⧸ maximalIdeal R) := Ideal.Quotient.field (maximalIdeal R)
  have : Module.Finite R (T ⧸ I) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ R I).toLinearMap Ideal.Quotient.mk_surjective
  have : Module.Finite (R ⧸ maximalIdeal R) (T ⧸ I) :=
    Module.Finite.of_restrictScalars_finite R _ _
  have : IsArtinianRing (T ⧸ I) := IsArtinianRing.of_finite (R ⧸ maximalIdeal R) _
  exact IsLocalRing.exists_maximalIdeal_pow_le_of_isArtinianRing_quotient I

end SerrePositivity

end LocalExtension

section FiniteLocalSupport

namespace SerrePositivity

open IsLocalRing

/-- 剰余体への合成が全射なら、元の環準同型も局所準同型。 -/
lemma isLocalHom_of_residue_surjective
    {B T : Type u} [CommRing B] [IsLocalRing B] [CommRing T] [IsLocalRing T]
    (φ : B →+* T) (hres : Function.Surjective ((residue T).comp φ)) : IsLocalHom φ := by
  let := IsLocalHom.of_surjective ((residue T).comp φ) hres
  exact isLocalHom_of_comp φ (residue T)

/-- 共通剰余体の条件は、局所環の全射像に移る。 -/
lemma residue_surjective_comp_of_surjective
    {A D Z : Type u} [CommRing A] [CommRing D] [IsLocalRing D]
    [CommRing Z] [IsLocalRing Z] (f : A →+* D) (g : D →+* Z)
    (hf : Function.Surjective ((residue D).comp f)) (hg : Function.Surjective g) :
    Function.Surjective ((residue Z).comp (g.comp f)) := by
  let := IsLocalHom.of_surjective g hg
  intro z
  obtain ⟨d, hd⟩ := (residue_surjective.comp hg) z
  obtain ⟨a, ha⟩ := hf (residue D d)
  refine ⟨a, ?_⟩
  change residue Z (g (f a)) = z
  rw [← ResidueField.map_residue, show residue D (f a) = residue D d from ha,
    ResidueField.map_residue]
  exact hd

/-- 有限局所代数では、基底の極大イデアルの生成元の像が閉点を定める。 -/
lemma maximalIdeal_le_radical_span_of_finite
    {B : Type u} [CommRing B] [IsLocalRing B]
    (T : Type u) [CommRing T] [IsLocalRing T] [Algebra B T] [Module.Finite B T]
    {f : ℕ} (z : Fin f → B) (hz : Ideal.span (Set.range z) = maximalIdeal B) :
    maximalIdeal T ≤ (Ideal.span (Set.range (algebraMap B T ∘ z))).radical := by
  obtain ⟨n, hn⟩ := maximalIdeal_pow_le_map_of_finite T (R := B)
  have hmap : (maximalIdeal B).map (algebraMap B T) =
      Ideal.span (Set.range (algebraMap B T ∘ z)) := by
    rw [← hz, Ideal.map_span, Set.range_comp]
  intro x hx
  exact Ideal.mem_radical_iff.mpr ⟨n, hmap ▸ hn (Ideal.pow_mem_pow hx n)⟩

/-- 有限余長のイデアルは、極大イデアルの生成元の正の共通冪を含む。 -/
lemma exists_maximal_generators_pow_mem
    {B : Type u} [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
    (I : Ideal B) (hI : Module.length B (B ⧸ I) ≠ ⊤) :
    ∃ (f : ℕ) (z : Fin f → B) (N : ℕ),
      Ideal.span (Set.range z) = maximalIdeal B ∧ 0 < N ∧ ∀ j, z j ^ N ∈ I := by
  obtain ⟨f, z, hz⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (maximalIdeal B).fg_of_isNoetherianRing
  have hlen := Module.length_ne_top_iff.mp hI
  have : IsArtinian B (B ⧸ I) := (isFiniteLength_iff_isNoetherian_isArtinian.mp hlen).2
  have : IsArtinianRing (B ⧸ I) := isArtinian_of_tower B inferInstance
  obtain ⟨n, hn⟩ := exists_maximalIdeal_pow_le_of_isArtinianRing_quotient I
  refine ⟨f, z, n + 1, hz, by omega, fun j ↦ ?_⟩
  have hj : z j ∈ maximalIdeal B := hz ▸ Ideal.subset_span (Set.mem_range_self j)
  simpa only [pow_succ] using I.mul_mem_right (z j) (hn (Ideal.pow_mem_pow hj n))

/-- 有限局所代数が基底の極大イデアルの冪で消えるなら、Artin 環である。 -/
lemma isArtinianRing_of_finite_killed_maximal_pow
    (A Z : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [CommRing Z] [Algebra A Z] [Module.Finite A Z] {n : ℕ}
    (hkill : ∀ r ∈ maximalIdeal A ^ n, algebraMap A Z r = 0) : IsArtinianRing Z := by
  have : IsArtinianRing (A ⧸ maximalIdeal A) :=
    inferInstanceAs (IsArtinianRing (ResidueField A))
  have hlen : IsFiniteLength A Z :=
    isFiniteLength_of_le_radical_annihilator (maximalIdeal A) Z fun r hr ↦
      Ideal.mem_radical_iff.mpr ⟨n, Module.mem_annihilator.mpr fun z ↦ by
        rw [Algebra.smul_def, hkill _ (Ideal.pow_mem_pow hr n), zero_mul]⟩
  exact isArtinian_of_tower A (isFiniteLength_iff_isNoetherian_isArtinian.mp hlen).2

/-- Artin 局所環への写像が剰余体で全射なら、その核は有限余長である。 -/
lemma length_quotient_ker_ne_top_of_common_residue
    {B Z : Type u} [CommRing B] [CommRing Z] [IsLocalRing Z] [IsArtinianRing Z]
    [Algebra B Z] (hres : Function.Surjective ((residue Z).comp (algebraMap B Z))) :
    Module.length B (B ⧸ RingHom.ker (algebraMap B Z)) ≠ ⊤ := by
  have hZ : Module.length B Z ≠ ⊤ := by
    rw [length_eq_of_common_residueField hres Z]
    exact Module.length_ne_top_iff.mpr
      (isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩)
  exact ne_top_of_le_ne_top hZ (Module.length_le_of_injective
    (Ideal.kerLiftAlg (Algebra.ofId B Z)).toLinearMap
    (Ideal.kerLiftAlg_injective _))

end SerrePositivity

end FiniteLocalSupport
