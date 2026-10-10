module

public import SerrePositivity.CommutativeAlgebra.FiniteLength
public import Mathlib.RingTheory.KrullDimension.Module
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.Finiteness.Basic

/-!
# 局所環上の有限代数

## 概要

局所環 `R` とその上の有限代数 `T`（局所環）、および素イデアル `I` による商環 `R ⧸ I` 上の加群に
ついて、零化イデアル・台の次元・剰余体・極大イデアルの冪に関する小さな事実を集める。論文の設定
（`A ⊆ D` が有限で剰余体が同じ、`T` が `A` 上有限）で、正規化長さの定義域を取り替えたり、加群の
台の次元を調べたりするときに使う。

## 内容

- 商環 `R ⧸ I` 上の加群は `I` で消える（`quotient_action_annihilator`）。商加群の零化イデアルは
  元の零化イデアルを含む（`annihilator_le_quotient`）。
- 素イデアル `I` による商環 `R ⧸ I` 上で正の階数をもつ有限生成 `R` 加群の台の次元は `dim(R ⧸ I)`
  （`supportDim_of_quotient_rank_pos`）。局所性も正則性も要らない。Lemma 5.2 で、`D'` 上の階数が
  正の加群の次元を言うのに使う。
- 整域 `R ⧸ I` 上の有限生成ねじれ加群の台の次元は `dim(R ⧸ I)` より真に小さい
  （`supportDim_add_one_le_of_quotient_torsion`）。一般点の基底から自由部分加群を作ると、余核は
  ねじれ加群なので次元が落ちる（`exists_genericBasis`）。
- 剰余体への射 `R → T → T/m_T` が全射なら、剰余体の同型 `ResidueField R ≃+* ResidueField T` がある
  （`residueFieldEquiv_of_surjective`）。
- 局所環 `R` 上有限な局所環 `T` では、`m_T` のある冪が `m_R T` に入る
  （`maximalIdeal_pow_le_map_of_finite`）：`T ⧸ m_R T` は体 `R ⧸ m_R` 上有限次元なので Artin 環で、
  Artin 局所環の極大イデアルは冪零だから。正規化長さの定義域のイデアルを `m_R C` と `m_T C` の
  間で取り替えるのに使う（`PowTorsion.lean` の `of_pow_le`。`Paper/Lemma3_4.lean`、
  `Paper/Corollary2_6.lean`、`Paper/Section5/NormApplication.lean`）。
-/

@[expose] public section

universe u

open IsLocalRing

namespace SerrePositivity

variable {R : Type u} [CommRing R]

/-- 加群 `M` が `R ⧸ I` 加群の構造をもち、`R` の作用がそれを経由する（`IsScalarTower`）なら、`I` は
`M` を消す：`r ∈ I` は `R ⧸ I` で零になるから。 -/
lemma quotient_action_annihilator (I : Ideal R) (M : Type u) [AddCommGroup M]
    [Module R M] [Module (R ⧸ I) M] [IsScalarTower R (R ⧸ I) M] :
    I ≤ Module.annihilator R M := by
  intro r hr
  rw [Module.mem_annihilator]
  intro x
  rw [← IsScalarTower.algebraMap_smul (R ⧸ I) r x]
  have hz : algebraMap R (R ⧸ I) r = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hr
  rw [hz, zero_smul]

/-- 素イデアル `I` による商環 `R ⧸ I` 上で正の階数をもつ有限生成 `R` 加群 `M`（`R ⧸ I` 加群の構造が
`R` の作用と両立するもの）について、台の次元 `dim Supp M` は `dim(R ⧸ I)` に等しい。階数が正なら
`R ⧸ I`（整域）の作用は忠実なので `Ann_R M = I`、そして台の次元は `dim(R ⧸ Ann M)` に等しい
（Mathlib の `supportDim_eq_ringKrullDim_quotient_annihilator`）。正則性も局所性も要らない。
Lemma 5.2（`IntersectionMultiplicity/FiniteExtension.lean`）で次元の条件を確かめるのに使う。 -/
theorem supportDim_of_quotient_rank_pos (I : Ideal R) [I.IsPrime]
    (M : Type u) [AddCommGroup M] [Module R M] [Module (R ⧸ I) M]
    [IsScalarTower R (R ⧸ I) M] [Module.Finite R M]
    (hr : 0 < Module.finrank (R ⧸ I) M) :
    Module.supportDim R M = ringKrullDim (R ⧸ I) := by
  have hf : FaithfulSMul (R ⧸ I) M := by
    by_contra hn
    exact hr.ne' (Module.finrank_eq_zero_of_not_faithfulSMul hn)
  have hann : Module.annihilator R M = I := by
    rw [← Module.comap_annihilator (R := R ⧸ I), Module.annihilator_eq_bot.mpr hf]
    ext x
    simp [Ideal.Quotient.eq_zero_iff_mem]
  rw [Module.supportDim_eq_ringKrullDim_quotient_annihilator, hann]

/-- 商加群の零化イデアルは元の零化イデアルを含む。 -/
lemma annihilator_le_quotient (M : Type u) [AddCommGroup M] [Module R M]
    (N : Submodule R M) : Module.annihilator R M ≤ Module.annihilator R (M ⧸ N) := by
  intro r hr
  rw [Module.mem_annihilator] at hr ⊢
  intro x
  obtain ⟨x, rfl⟩ := N.mkQ_surjective x
  rw [← N.mkQ.map_smul, hr, map_zero]

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
