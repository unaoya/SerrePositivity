module

public import SerrePositivity.HomologicalAlgebra.BaseChange
public import Mathlib.Algebra.CharP.Frobenius
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.Topology.Instances.ENNReal.Lemmas

/-! # Roberts の Frobenius ホモロジー消滅定理（文献からの引用）

完備 Noether 局所環上で、長さが環の次元に等しい有限自由複体に対する
高次 Frobenius ホモロジーの正規化長さの消滅を、名前付きの未証明定理として置く。
出典は Roberts, *Intersection theorems* (1989) の結果を述べた
Ma, *Lech's conjecture in dimension three*, Theorem 2.4
（https://arxiv.org/html/1609.00095v3）。

文献の homological 次数 `i` を cochain 次数 `-i` とし、長さ `d` の複体は
`[-d, 0]` の外で零と書く。Frobenius 関手は `iterateFrobenius` に沿う基底変更である。
Koszul 複体への適用条件、パラメータの冪との同定、perfection への移送は引用に含めず、
`CommutativeAlgebra/FrobeniusKoszulLimit.lean` と `Paper/Section2/` で証明する。
-/

public section

universe u

namespace SerrePositivity.Inputs

open CategoryTheory Limits IsLocalRing Filter

/-- Roberts の消滅定理（引用、未証明）。完備 Noether 局所環の次元 `d` と同じ長さの
有限自由複体でホモロジーが有限長なら、正次数の Frobenius ホモロジーの長さを
`p^(nd)` で割った実数値の列は零へ収束する。 -/
theorem frobenius_homology_length_tendsto_zero
    (D : Type u) [CommRing D] [IsLocalRing D] [IsNoetherianRing D]
    [IsAdicComplete (maximalIdeal D) D]
    (p : ℕ) [Fact p.Prime] [CharP D p]
    (d : ℕ) (hdim : ringKrullDim D = d)
    (K : CochainComplex (ModuleCat.{u} D) ℤ)
    (hfree : ∀ j, Module.Free D (K.X j) ∧ Module.Finite D (K.X j))
    (hbound : ∀ j, j < -(d : ℤ) ∨ 0 < j → IsZero (K.X j))
    (hfinite : ∀ j, IsFiniteLength D (K.homology j))
    (i : ℕ) (hi : 0 < i) :
    Tendsto (fun n : ℕ ↦
      ((Module.length D
        ((baseChange (iterateFrobenius D p n) K).homology (-(i : ℤ)))).toNat : ℝ) /
          (p : ℝ) ^ (n * d)) atTop (nhds 0) := by
  sorry

end SerrePositivity.Inputs
