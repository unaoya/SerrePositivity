module

public import SerrePositivity.CommutativeAlgebra.LocalAlgebra
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-! # 有限局所代数への支持条件の移送

剰余体への全射性から局所性を、有限性から閉点の根基条件を得る。
有限余長の消去イデアルからは、極大イデアルの有限生成系と正の共通消去冪を選ぶ。
有限近似の支持を確認する際の、圏や長さ関数によらない準備である。
-/

@[expose] public section

universe u

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
