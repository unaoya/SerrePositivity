module

public import SerrePositivity.CommutativeAlgebra.PerfectoidizationMap
public import SerrePositivity.CommutativeAlgebra.PerfectoidPTorsion

/-! # pの正冪と単元倍によるperfectoidイデアルの比較

perfectoid化の普遍性と、pが冪零ならp=0という証明から、pの正冪のイデアルを比較する。
差のalmost零性の一般的な主張はここに仮定として追加しない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity
variable (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime]
    (hR : IsIntegralPerfectoid R p)

/-- kがgのperfectoidイデアルに入れば、kのperfectoidイデアルもそこに含まれる。 -/
theorem perfectoidIdeal_le_of_mem {g k : R} (hk : k ∈ perfectoidIdeal R p hR g) :
    perfectoidIdeal R p hR k ≤ perfectoidIdeal R p hR g := by
  let : Algebra.FinitePresentation R (R ⧸ Ideal.span {g}) :=
    Algebra.FinitePresentation.quotient (Submodule.fg_span_singleton g)
  let : Algebra.FinitePresentation R (R ⧸ Ideal.span {k}) :=
    Algebra.FinitePresentation.quotient (Submodule.fg_span_singleton k)
  let T := QuotientPerfectoidization R (Ideal.span {g}) p hR
  let κ : R →+* T := (toQuotientPerfectoidization R (Ideal.span {g}) p hR).comp
    (Ideal.Quotient.mk (Ideal.span {g}))
  let f : R ⧸ Ideal.span {k} →+* T := Ideal.Quotient.lift _ κ
    ((Ideal.span_singleton_le_iff_mem _).mpr hk)
  let hg := isPerfectoidization_toQuotientPerfectoidization R (Ideal.span {g}) p hR
  let hk' := isPerfectoidization_toQuotientPerfectoidization R (Ideal.span {k}) p hR
  let l := IsPerfectoidization.lift hk' hg.1 f
  intro x hx
  change toQuotientPerfectoidization R (Ideal.span {k}) p hR
    (Ideal.Quotient.mk (Ideal.span {k}) x) = 0 at hx
  change κ x = 0
  have he := RingHom.congr_fun (IsPerfectoidization.lift_comp hk' hg.1 f)
    (Ideal.Quotient.mk (Ideal.span {k}) x)
  rw [RingHom.comp_apply, hx, map_zero] at he
  exact he.symm

/-- pの正冪のperfectoidイデアルはp自身のperfectoidイデアルと一致する。 -/
theorem perfectoidIdeal_p_pow_eq (n : ℕ) (hn : 0 < n) :
    perfectoidIdeal R p hR ((p : R) ^ n) = perfectoidIdeal R p hR (p : R) := by
  let : Algebra.FinitePresentation R (R ⧸ Ideal.span {(p : R) ^ n}) :=
    Algebra.FinitePresentation.quotient (Submodule.fg_span_singleton ((p : R) ^ n))
  let T := QuotientPerfectoidization R (Ideal.span {(p : R) ^ n}) p hR
  let κ : R →+* T := (toQuotientPerfectoidization R (Ideal.span {(p : R) ^ n}) p hR).comp
    (Ideal.Quotient.mk (Ideal.span {(p : R) ^ n}))
  have hT : IsIntegralPerfectoid T p :=
    (isPerfectoidization_toQuotientPerfectoidization R (Ideal.span {(p : R) ^ n}) p hR).1
  have hz : (p : T) ^ n = 0 := by
    have hh := (span_le_perfectoidIdeal R p hR ((p : R) ^ n))
      (Ideal.subset_span (Set.mem_singleton _))
    change κ ((p : R) ^ n) = 0 at hh
    simpa only [map_pow, map_natCast] using hh
  have hp0 : (p : T) = 0 := hT.p_eq_zero_of_isNilpotent T p ⟨n, hz⟩
  apply le_antisymm
  · apply perfectoidIdeal_mono
    apply (Ideal.span_singleton_le_iff_mem _).mpr
    exact Ideal.pow_mem_of_mem _ (Ideal.subset_span (Set.mem_singleton _)) _ hn
  · apply perfectoidIdeal_le_of_mem
    change κ (p : R) = 0
    simpa only [map_natCast] using hp0

/-- 単元倍はperfectoidイデアルを変えない。 -/
theorem perfectoidIdeal_mul_unit_eq (g a : R) (ha : IsUnit a) :
    perfectoidIdeal R p hR (g * a) = perfectoidIdeal R p hR g := by
  have hs : Ideal.span {g * a} = Ideal.span {g} := Ideal.span_singleton_mul_right_unit ha g
  exact le_antisymm (perfectoidIdeal_mono R p hR hs.le)
    (perfectoidIdeal_mono R p hR hs.ge)

end SerrePositivity
