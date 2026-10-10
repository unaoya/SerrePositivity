module

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
public import Mathlib.RingTheory.KrullDimension.Basic

/-!
# 正則局所環の非混合性という未証明入力

正則局所環 `R`（Cohen–Macaulay）の正則列 `r_1, …, r_i` について、`R/(r_1, …, r_i)` の
随伴素イデアル `p` はすべて `dim R/p = dim R − i` をみたす（非混合性定理）。
論文 §5.2 の (5.4) で、`Q` の元を正則列として選ぶ素イデアル回避に使う。

文献：Matsumura, *Commutative Ring Theory*, Theorem 17.3 (i) と 17.4、
Bruns–Herzog, *Cohen–Macaulay Rings*, Theorem 2.1.2 と 2.1.6。
-/

@[expose] public section

universe u

namespace SerrePositivity

/-- **非混合性**（未証明、引用）：正則局所環 `R` の弱正則列 `rs` について、`R/(rs)` の随伴素イデアル
`p` は `dim R/p + |rs| = dim R` をみたす。`R` は Cohen–Macaulay なので `R/(rs)` も次元
`dim R − |rs|` の Cohen–Macaulay 加群で、Cohen–Macaulay 加群の随伴素イデアル `p` は
`dim R/p = dim M` をみたす（Matsumura Thm 17.3 (i)）。 -/
theorem ringKrullDim_quotient_add_length_of_mem_associatedPrimes {R : Type u} [CommRing R]
    [IsRegularLocalRing R] (rs : List R) (_hrs : RingTheory.Sequence.IsWeaklyRegular R rs)
    {p : Ideal R} (_hp : p ∈ associatedPrimes R (R ⧸ Ideal.ofList rs)) :
    ringKrullDim (R ⧸ p) + rs.length = ringKrullDim R := by
  sorry

end SerrePositivity
