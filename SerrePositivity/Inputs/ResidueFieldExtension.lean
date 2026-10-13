module

public import SerrePositivity.CommutativeAlgebra.ResidueFieldGeneralCompletion

/-! # 指定した剰余体を持つ完備平坦局所拡大（証明済み）

既存入口の型を保ち、環の存在を実構成から証明する。加群の長さ、次元、正則性、Tor の保存は含めない。
それらは `CommutativeAlgebra/FlatLocalDimension` と
`IntersectionMultiplicity/BaseChange` から補題2.1で導く。
-/

public section

universe u

namespace SerrePositivity.Inputs

open IsLocalRing

/-- **証明済み：剰余体拡大の持ち上げ（完備 Noether 版）。**
EGA I, 2nd ed., 0, Proposition 6.8.3（gonflement）。
Stacks Project, Tag 03C3 の平坦局所拡大を完備化した形である。
現在は一般拡大の実図式、adic Noether判定、共通の完備化の平坦性から証明する。
上の文献は元の引用の参照先であり、この入口の未証明入力ではない。
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
  exact SerrePositivity.exists_complete_flat_local_extension_of_residueField B K

end SerrePositivity.Inputs
