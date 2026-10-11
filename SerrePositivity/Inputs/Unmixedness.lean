module

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
public import Mathlib.RingTheory.KrullDimension.Basic
public import SerrePositivity.CommutativeAlgebra.RegularSequenceUnmixedness

/-!
# 正則局所環の正則列商の非混合性

正則局所環 `R`（Cohen–Macaulay）の正則列 `r_1, …, r_i` について、`R/(r_1, …, r_i)` の
随伴素イデアル `p` はすべて `dim R/p = dim R − i` をみたす（非混合性定理）。
論文 §5.2 の (5.4) で、`Q` の元を正則列として選ぶ素イデアル回避に使う。

`RegularSequenceUnmixedness.lean` の証明を既存の公開名で参照する。
Krull 共通部分から随伴素イデアルの商への移行を示し、正則列の長さの上界から
深さの上界を導く。正則元の短完全列による深さの下界と、正則列商の次元公式を合わせる。

文献：Matsumura, *Commutative Ring Theory*, Theorem 17.3 (i) と 17.4、
Bruns–Herzog, *Cohen–Macaulay Rings*, Theorem 2.1.2 と 2.1.6。
-/

@[expose] public section

universe u

namespace SerrePositivity

/-- **非混合性**：正則局所環 `R` の弱正則列 `rs` について、`R/(rs)` の随伴素イデアル
`p` は `dim R/p + |rs| = dim R` をみたす。`R` は Cohen–Macaulay なので `R/(rs)` も次元
`dim R − |rs|` の Cohen–Macaulay 加群で、Cohen–Macaulay 加群の随伴素イデアル `p` は
`dim R/p = dim M` をみたす（Matsumura Thm 17.3 (i)）。ここでは必要な深さと次元の
上下界を証明して接続し、一般の Cohen–Macaulay 理論を入力にはしない。 -/
theorem ringKrullDim_quotient_add_length_of_mem_associatedPrimes {R : Type u} [CommRing R]
    [IsRegularLocalRing R] (rs : List R) (hrs : RingTheory.Sequence.IsWeaklyRegular R rs)
    {p : Ideal R} (hp : p ∈ associatedPrimes R (R ⧸ Ideal.ofList rs)) :
    ringKrullDim (R ⧸ p) + rs.length = ringKrullDim R :=
  RegularSequenceUnmixedness.dimension_eq rs hrs hp

end SerrePositivity
