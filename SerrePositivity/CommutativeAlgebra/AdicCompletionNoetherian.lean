module

public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.AdicCompletion.Functoriality
public import Mathlib.RingTheory.AdicCompletion.Topology
public import SerrePositivity.CommutativeAlgebra.AdicPowerSeries
public import Mathlib.RingTheory.MvPowerSeries.Equiv

/-! # Noether 環のイデアル進完備化の Noether 性

有限生成イデアル `J` に関して完備な環 `S` に Noether 環 `R` から写像があり、
`R → S/J` が全射なら、有限変数の形式冪級数環から `S` への全射が得られる。
これにより `S` は Noether 環である。`R` の任意のイデアルに関する完備化に適用する。
未証明入力を使わず、§5 の一般の正則局所環から完備な場合への帰着を支える。
-/

public section

namespace SerrePositivity

/-- 有限生成イデアルに関して完備な環は、Noether な係数環がその商に全射なら Noether。
イデアルの生成元に形式変数を送る評価写像を、完備性によって全射にする。 -/
theorem isNoetherianRing_of_adicComplete_of_surjective_quotient
    (R S : Type*) [CommRing R] [CommRing S] [IsNoetherianRing R]
    (f : R →+* S) (J : Ideal S) [IsAdicComplete J S]
    (hJ : J.FG) (hf : Function.Surjective ((Ideal.Quotient.mk J).comp f)) :
    IsNoetherianRing S := by
  classical
  obtain ⟨s, hs⟩ := hJ
  let x : s → S := fun i ↦ i.val
  have hx : Ideal.span (Set.range x) = J := by
    simpa [x] using hs
  have hmem (i : s) : x i ∈ J := by
    rw [← hx]
    exact Ideal.subset_span ⟨i, rfl⟩
  let g := adicPowerSeriesEval f J x hmem
  have hsurj : Function.Surjective g := adicPowerSeriesEval_surjective f J x hmem hx hf
  exact isNoetherianRing_of_surjective _ _ g hsurj

/-- Noether 環の任意のイデアルに関するイデアル進完備化は Noether 環である。 -/
theorem isNoetherianRing_adicCompletion (R : Type*) [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) : IsNoetherianRing (AdicCompletion I R) := by
  let S := AdicCompletion I R
  let J := I.map (algebraMap R S)
  have : IsAdicComplete I S := AdicCompletion.isAdicComplete (M := R) I.fg_of_isNoetherianRing
  have : IsAdicComplete J S := (IsAdicComplete.map_algebraMap_iff (S := S) I S).mpr inferInstance
  apply isNoetherianRing_of_adicComplete_of_surjective_quotient R S (algebraMap R S) J
    (I.fg_of_isNoetherianRing.map _)
  intro z
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalOneₐ I y)
  refine ⟨r, Ideal.Quotient.eq.mpr ?_⟩
  change algebraMap R S r - y ∈ I.map (algebraMap R S)
  rw [← AdicCompletion.ker_evalOneₐ_eq_map I I.fg_of_isNoetherianRing]
  change AdicCompletion.evalOneₐ I (algebraMap R S r - y) = 0
  rw [map_sub]
  exact sub_eq_zero.mpr hr

end SerrePositivity
