module

public import SerrePositivity.CommutativeAlgebra.AssociatedPrimeDimension
public import SerrePositivity.CommutativeAlgebra.Depth
public import SerrePositivity.CommutativeAlgebra.RegularLocalRing.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs

/-! # 正則局所環の正則列商の非混合性

## 概要

正則局所環 `R`（Cohen–Macaulay）の弱正則列 `r_1, …, r_i` について、`R/(r_1, …, r_i)` の
随伴素イデアル `p` はすべて `dim R/p + i = dim R` をみたす
（`ringKrullDim_quotient_add_length_of_mem_associatedPrimes`、非混合性定理）。
あわせて、正則局所環の深さは次元以上（`dimToNat_le_depth`）。

## 方針

上界：随伴素イデアル `p` について `dim R/p ≤ dim R/(rs)`、そして正則列商の次元公式
`dim R/(rs) + |rs| = dim R`。下界：正則局所環には次元と同数の正則な極大イデアル生成元があるので
深さは次元以上で、正則列で割ったときの深さの減り方（`Depth`）と `depth ≤ dim R/p` を合わせる。

## 規約

一般の Cohen–Macaulay 理論は使わず、必要な深さと次元の上下界だけを示して接続する。
文献：Matsumura, *Commutative Ring Theory*, Theorem 17.3 (i) と 17.4、
Bruns–Herzog, *Cohen–Macaulay Rings*, Theorem 2.1.2 と 2.1.6。

## 使われ方

論文 §5.2 の (5.4) で、`Q` の元を正則列として選ぶ素イデアル回避（`ParameterAvoidance`、
`Inputs/Unmixedness`）と、正則局所環の素イデアルの次元公式（`RegularPrimeDimension`）。
-/

@[expose] public section

universe u

open IsLocalRing RingTheory.Sequence

namespace SerrePositivity

section Depth

/-- 正則局所環の深さは Krull 次元以上である。最小正則生成列の存在から従う。 -/
theorem dimToNat_le_depth (R : Type u) [CommRing R] [IsRegularLocalRing R] :
    (dimToNat (ringKrullDim R) : ℕ∞) ≤ IsLocalRing.depth (ModuleCat.of R R) := by
  obtain ⟨rs, hrs, hgen, hdim⟩ := exists_regular_generators R
  have hproper : Ideal.ofList rs ≠ ⊤ := hgen ▸ (maximalIdeal.isMaximal R).ne_top
  have hmem : ∀ x ∈ rs, x ∈ maximalIdeal R :=
    fun x hx ↦ le_maximalIdeal hproper (Ideal.subset_span hx)
  have hreg : IsRegular R rs :=
    (IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal hmem).mpr hrs
  have hlen : dimToNat (ringKrullDim R) = rs.length := by
    rw [hdim]
    simp [dimToNat]
  rw [hlen, IsLocalRing.depth_eq_sSup_length_isRegular]
  exact le_sSup ⟨rs, hreg, hmem, rfl⟩

/-- 非混合性の適用で必要になる、正則列商の深さの次元による下界。 -/
theorem dimToNat_le_depth_ringQuotient_add_length
    (R : Type u) [CommRing R] [IsRegularLocalRing R]
    (rs : List R) (hrs : IsWeaklyRegular R rs) :
    (dimToNat (ringKrullDim R) : ℕ∞) ≤
      IsLocalRing.depth (ModuleCat.of R (R ⧸ Ideal.ofList rs)) + rs.length := by
  have h := (dimToNat_le_depth R).trans (depth_le_depth_quotient_add_length R rs hrs)
  have heq : (Ideal.ofList rs • ⊤ : Submodule R R) = Ideal.ofList rs := by
    rw [Ideal.smul_eq_mul, Ideal.mul_top]
  rwa [heq] at h

end Depth

/-- **非混合性**：正則局所環 `R` の弱正則列 `rs` について、`R/(rs)` の随伴素イデアル
`p` は `dim R/p + |rs| = dim R` をみたす。`R` は Cohen–Macaulay なので `R/(rs)` も次元
`dim R − |rs|` の Cohen–Macaulay 加群で、Cohen–Macaulay 加群の随伴素イデアル `p` は
`dim R/p = dim M` をみたす（Matsumura Thm 17.3 (i)）。ここでは必要な深さと次元の
上下界を証明して接続し、一般の Cohen–Macaulay 理論を入力にはしない。 -/
theorem ringKrullDim_quotient_add_length_of_mem_associatedPrimes {R : Type u} [CommRing R]
    [IsRegularLocalRing R] (rs : List R) (hrs : RingTheory.Sequence.IsWeaklyRegular R rs)
    {p : Ideal R} (hp : p ∈ associatedPrimes R (R ⧸ Ideal.ofList rs)) :
    ringKrullDim (R ⧸ p) + rs.length = ringKrullDim R := by
  have hreg := AssociatedPrimeDimension.isRegular_of_isWeaklyRegular_of_mem_associatedPrimes
    rs hrs hp
  have hupper := AssociatedPrimeDimension.ringKrullDim_quotient_le_supportDim hp
  rw [Module.supportDim_quotient_eq_ringKrullDim] at hupper
  have hdim := ringKrullDim_add_length_eq_ringKrullDim_of_isRegular rs hreg
  apply le_antisymm ((add_le_add hupper le_rfl).trans_eq hdim)
  have hdepth := dimToNat_le_depth_ringQuotient_add_length R rs hrs
  have hdepth' : (dimToNat (ringKrullDim R) : WithBot ℕ∞) ≤
      (IsLocalRing.depth (ModuleCat.of R (R ⧸ Ideal.ofList rs)) : WithBot ℕ∞) + rs.length := by
    exact_mod_cast hdepth
  rw [natCast_dimToNat_ringKrullDim R] at hdepth'
  exact hdepth'.trans (add_le_add
    (depth_le_dim_quotient_of_mem_associatedPrimes (ModuleCat.of R (R ⧸ Ideal.ofList rs)) hp)
    le_rfl)

end SerrePositivity
