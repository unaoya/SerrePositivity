module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Noetherian.Defs

/-! # 引用：指定した剰余体を持つ完備平坦局所拡大

引用するのは環の存在のみ。加群の長さ、次元、正則性、Tor の保存は含めない。
それらは `CommutativeAlgebra/FlatLocalDimension` と
`IntersectionMultiplicity/BaseChange` から補題2.1で導く。
-/

public section

universe u

namespace SerrePositivity.Inputs

open IsLocalRing

/-- **引用：剰余体拡大の持ち上げ（完備 Noether 版）。**
EGA I, 2nd ed., 0, Proposition 6.8.3（gonflement）。
Stacks Project, Tag 03C3 の平坦局所拡大を完備化した形である。
完備化の Noether 性・平坦性もこの引用の範囲に含む。
Tag 03C3 単独では拡大環の完備性・Noether 性まで主張していない。
出典：https://stacks.math.columbia.edu/tag/03C3

基底環自体の完備性は不要。体の同型には元の剰余体上での両立性を要求する。 -/
theorem exists_complete_flat_local_extension
    (B : Type u) [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
    (K : Type u) [Field K] [Algebra (ResidueField B) K] :
    ∃ (B' : Type u) (_ : CommRing B') (_ : IsLocalRing B') (_ : IsNoetherianRing B')
      (_ : IsAdicComplete (maximalIdeal B') B') (_ : Algebra B B')
      (_ : IsLocalHom (algebraMap B B')),
      Module.Flat B B' ∧ (maximalIdeal B).map (algebraMap B B') = maximalIdeal B' ∧
      ∃ e : ResidueField B' ≃+* K,
        ∀ x, e (ResidueField.map (algebraMap B B') x) =
          algebraMap (ResidueField B) K x := by
  sorry

end SerrePositivity.Inputs
