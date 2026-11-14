module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.HomologicalAlgebra.TorLES
public import Mathlib.RingTheory.Finiteness.Cardinality
public import Mathlib.RingTheory.TensorProduct.Finite
public import Mathlib.RingTheory.Support
public import SerrePositivity.CommutativeAlgebra.Length.Basic
public import SerrePositivity.CommutativeAlgebra.PowerTorsion.Basic
public import SerrePositivity.CommutativeAlgebra.SupportDimension

/-!
# Tor の有限生成性・台・有限長性と冪ねじれ性

Noether 環上の有限生成加群どうしの Tor は有限生成で、その台は両変数の台の共通部分に含まれる。
テンソル積が有限長なら、この共通部分には極大イデアルしか現れないので、各 Tor も有限長である。
`isFiniteLength_torModule` はこの一般定理であり、正則性や有界有限自由分解の存在は仮定しない。


局所環 `A` 上の有限長加群 `V` について、`Tor_i^A(C, V)`（`TorAlg φ i V`）は `m_A C`（`m_A` の `C` への
拡大）のある冪で消える（`torAlg_isPowTorsion`）。有限長加群は `m_A` の冪 `m_A^n` で消え
（`FiniteLength.lean`）、`V` を消す元は `Tor` も消す（`HomologicalAlgebra/Tor.lean` の
`torAlg_smul_eq_zero`）ことによる。これで `Tor_i^A(C, V)` が正規化長さ `λ`（定義域は `m_A C` 冪ねじれ
加群）で測れることが保証され、Lemma 3.4 と Corollary 2.6
（`IntersectionMultiplicity/NormalizedTor.lean`）で使う。
-/

@[expose] public section

universe u

open IsLocalRing

namespace SerrePositivity

open CategoryTheory in
/-- Noether 環上の有限生成加群どうしの Tor は、各次数で有限生成である。
有限自由加群から第2変数への全射を取り、その核も有限生成であることを用いて次数で帰納する。
自由加群の高次 Tor は零なので、長完全列の連結射により一つ低い次数の Tor に単射を得る。
正則性や有界な自由分解は不要である。 -/
theorem finite_torModule {R : Type u} [CommRing R] [IsNoetherianRing R]
    (M : Type u) [AddCommGroup M] [Module R M]
    [Module.Finite R M] (i : ℕ) (N : Type u) [AddCommGroup N] [Module R N]
    [Module.Finite R N] : Module.Finite R (TorModule R i M N) := by
  induction i generalizing N with
  | zero => exact Module.Finite.equiv (torModuleZeroEquiv R M N).symm
  | succ i ih =>
    obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R N
    obtain ⟨α, β, δ, hαβ, hβδ, hδα, hβ⟩ := torModule_longExact M
      (LinearMap.ker f).subtype f (Submodule.injective_subtype _) hf
      (LinearMap.exact_subtype_ker_map f)
    have : Module.Finite R (TorModule R i M (LinearMap.ker f)) := ih _
    have : Projective (ModuleCat.of R (Fin n → R)) := inferInstance
    have hz := isZero_Tor_succ_of_projective (ModuleCat.{u} R)
      (ModuleCat.of R M) (ModuleCat.of R (Fin n → R)) i
    have : Subsingleton (TorModule R (i + 1) M (Fin n → R)) := ModuleCat.subsingleton_of_isZero hz
    apply Module.Finite.of_injective (δ i)
    exact (LinearMap.injective_iff_eq_zero_of_exact (hβδ i)).mpr (Subsingleton.elim _ _)

/-- 有限生成加群どうしの Tor の台は、二つの加群の台の共通部分に含まれる。
両方の零化イデアルが Tor を消すことと、有限生成加群の台の零化イデアルによる表示を使う。
この包含自体には Noether 性は不要である。 -/
theorem support_torModule_subset {R : Type u} [CommRing R] (i : ℕ)
    (M N : Type u) [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [Module.Finite R M] [Module.Finite R N] :
    Module.support R (TorModule R i M N) ⊆ Module.support R M ∩ Module.support R N := by
  intro p hp
  have h := Module.annihilator_le_of_mem_support hp
  exact ⟨Module.mem_support_iff_of_finite.mpr ((annihilator_le_torModule_left i M N).trans h),
    Module.mem_support_iff_of_finite.mpr ((annihilator_le_torModule_right i M N).trans h)⟩

open TensorProduct in
/-- Noether 環上の有限生成加群 `M, N` のテンソル積が有限長なら、すべての Tor も有限長である。
Tor の有限生成性と台の包含を用い、有限長性を台に属する素イデアルの極大性から導く。 -/
theorem isFiniteLength_torModule {R : Type u} [CommRing R] [IsNoetherianRing R] (M N : Type u)
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Finite R M] [Module.Finite R N] (h : IsFiniteLength R (M ⊗[R] N))
    (i : ℕ) : IsFiniteLength R (TorModule R i M N) := by
  have := finite_torModule (R := R) M i N
  apply isFiniteLength_of_support_isMaximal (R := R)
  intro p hp
  apply isMaximal_of_mem_support_of_isFiniteLength _ h p
  rw [support_tensorProduct]
  exact support_torModule_subset i M N hp

variable {A C : Type u} [CommRing A] [CommRing C] (φ : A →+* C)

variable [IsLocalRing A]

/-- 局所環 `A` 上の有限長加群 `V` について、`Tor_i^A(C, V)` は `(m_A C)^n` で消える `n` がある。
`V` が `m_A^n` で消えるので、`m_A^n` の各元 `a` について `φ(a)` が `Tor` を消し
（`torAlg_smul_eq_zero`）、`(m_A C)^n = (m_A^n) C` はそのような `φ(a)` で生成されるから。 -/
lemma torAlg_isPowTorsion (i : ℕ) (V : Type u) [AddCommGroup V] [Module A V]
    (hV : IsFiniteLength A V) : IsPowTorsion ((maximalIdeal A).map φ) (TorAlg φ i V) := by
  obtain ⟨n, hn⟩ := IsFiniteLength.exists_isTorsionBySet_maximalIdeal_pow hV
  refine ⟨n, ?_⟩
  rw [Module.isTorsionBySet_iff_subset_annihilator, ← Ideal.map_pow, Ideal.map,
    SetLike.coe_subset_coe, Ideal.span_le]
  rintro _ ⟨a, ha, rfl⟩
  rw [SetLike.mem_coe, Module.mem_annihilator]
  intro x
  exact torAlg_smul_eq_zero φ i V a (fun v ↦ @hn v ⟨a, ha⟩) x

end SerrePositivity

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite Paper "Lemma 4.4"] _root_.SerrePositivity.torAlg_isPowTorsion
