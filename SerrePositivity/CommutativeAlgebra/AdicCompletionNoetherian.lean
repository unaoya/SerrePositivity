module

public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.AdicCompletion.Functoriality
public import Mathlib.RingTheory.AdicCompletion.Topology
public import SerrePositivity.CommutativeAlgebra.AdicPowerSeries
public import SerrePositivity.CommutativeAlgebra.AdicNoetherianCriterion
public import Mathlib.RingTheory.MvPowerSeries.Equiv

/-! # Noether 環のイデアル進完備化の Noether 性

有限生成イデアル `J` に関して完備な環 `S` に Noether 環 `R` から写像があり、
`R → S/J` が全射なら、商のNoether性を移し、一般のadic Noether判定を適用する。
係数sectionを要求せず、`S` は Noether 環となる。`R` の任意のイデアルに関する完備化に適用する。
未証明入力を使わず、§5 の一般の正則局所環から完備な場合への帰着を支える。
-/

public section

namespace SerrePositivity

/-- 有限生成イデアルに関して完備な環は、Noether な係数環がその商に全射なら Noether。
係数写像から商のNoether性を確認し、共通のadic Noether判定へ接続する。 -/
theorem isNoetherianRing_of_adicComplete_of_surjective_quotient
    (R S : Type*) [CommRing R] [CommRing S] [IsNoetherianRing R]
    (f : R →+* S) (J : Ideal S) [IsAdicComplete J S]
    (hJ : J.FG) (hf : Function.Surjective ((Ideal.Quotient.mk J).comp f)) :
    IsNoetherianRing S := by
  let : IsNoetherianRing (S ⧸ J) :=
    isNoetherianRing_of_surjective R (S ⧸ J) ((Ideal.Quotient.mk J).comp f) hf
  exact isNoetherianRing_of_adicComplete_of_noetherian_quotient S J hJ

/-- Noether 環の任意のイデアルに関するイデアル進完備化は Noether 環である。 -/
theorem isNoetherianRing_adicCompletion (R : Type*) [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) : IsNoetherianRing (AdicCompletion I R) := by
  let : IsNoetherianRing (R ⧸ I) :=
    isNoetherianRing_of_surjective R (R ⧸ I) (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  exact isNoetherianRing_adicCompletion_of_noetherian_quotient R I I.fg_of_isNoetherianRing

end SerrePositivity
