module

public import Mathlib.RingTheory.KrullDimension.Module
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.Topology.MetricSpace.Basic

/-!
# パラメータ系と Hilbert–Samuel 重複度

- `IsSystemOfParameters D z`：`z : Fin h → D` が局所環 `D` のパラメータ系。
  `h = dim D` かつ `(z)` が `m_D` 準素。
- `hilbertSamuelMultiplicity I M`：`e(I, M) = lim_n d! · length(M / Iⁿ M) / nᵈ`（`d = dim M`）。
  `Filter.limUnder` で定義し、極限の存在は証明しない（存在しなければ junk value）。
  論文 (2.5) の右辺「正で有限」は、使う側で別に仮定する。
-/

@[expose] public section

universe u

namespace SerrePositivity

/-- `WithBot ℕ∞` 値の次元を自然数に落とす。`⊥` と `⊤` は `0` になる。 -/
noncomputable def dimToNat (d : WithBot ℕ∞) : ℕ := (d.unbotD 0).toNat

variable (D : Type u) [CommRing D]

/-- `z : Fin h → D` が局所環 `D` のパラメータ系であること：`h = dim D` かつ `(z)` は `m_D` 準素。 -/
def IsSystemOfParameters [IsLocalRing D] {h : ℕ} (z : Fin h → D) : Prop :=
  ringKrullDim D = h ∧ (Ideal.span (Set.range z)).radical = IsLocalRing.maximalIdeal D

/-- Hilbert–Samuel 重複度 `e(I, M) = lim_n d! · length_D(M / Iⁿ M) / nᵈ`、`d = dim M`。 -/
noncomputable def hilbertSamuelMultiplicity (I : Ideal D) (M : Type u) [AddCommGroup M]
    [Module D M] : ℝ :=
  let d := dimToNat (Module.supportDim D M)
  Filter.limUnder Filter.atTop fun n : ℕ ↦
    ((d.factorial : ℝ) * ((Module.length D (M ⧸ (I ^ n • (⊤ : Submodule D M)))).toNat : ℝ))
      / (n : ℝ) ^ d

end SerrePositivity
