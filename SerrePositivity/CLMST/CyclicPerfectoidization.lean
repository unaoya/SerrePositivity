module

public import SerrePositivity.CommutativeAlgebra.ModPHypersurfaceGrowth
public import SerrePositivity.CommutativeAlgebra.FlatRegularQuotient
public import SerrePositivity.CommutativeAlgebra.RootTower.Completion
public import SerrePositivity.CommutativeAlgebra.RegularLocalRing.Graded
public import SerrePositivity.BhattScholze.PerfectoidIdeal.Basic
public import SerrePositivity.BhattScholze.PerfectoidIdeal.CompletedQuotient

/-! # pで割れない巡回商への全射性定理の適用条件

完備塔の平坦性でmod pの正則性を移し、巡回商のpの非零因子性と完備性を供給する。
全射性は証明済みの一般主イデアル商のperfectoid化から供給する。
選択対象の存在・普遍性はB3で証明済み。一般整代数の存在引用は使わない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.CLMST
open IsLocalRing Section2

theorem completedTowerCyclicQuotient_p_regular_and_complete
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {r : ℕ} (t : Fin (r + 2) → A) (p : ℕ) [Fact p.Prime]
    (ht : Ideal.span (Set.range t) = maximalIdeal A) (htp : t 0 = (p : A))
    (hdim : ringKrullDim A = r + 2) (hperf : IsIntegralPerfectoid (CompletedTower A t p) p)
    (g : A) (hpg : ¬ (p : A) ∣ g) :
    let Q := CompletedTower A t p ⧸ Ideal.span {algebraMap A (CompletedTower A t p) g}
    IsSMulRegular Q (p : Q) ∧ IsAdicComplete (Ideal.span {(p : Q)}) Q := by
  let C := CompletedTower A t p
  let := flat_completedTower_over_base A t p
  have ha : IsSMulRegular A (p : A) := by
    rw [← htp]
    exact HilbertSamuel.isSMulRegular_generator_of_span_eq_maximalIdeal A t ht hdim 0
  let B := A ⧸ Ideal.span {(p : A)}
  let : IsDomain B := modP_isDomain_of_parameters A t p ht htp hdim
  have hgA : IsSMulRegular B (Ideal.Quotient.mk (Ideal.span {(p : A)}) g) := by
    apply IsSMulRegular.of_ne_zero
    intro hz
    exact hpg (Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hz))
  have hgC' := isSMulRegular_mod_of_flat (S := C) (p : A) g ha hgA
  have hI : Ideal.span {algebraMap A C (p : A)} = Ideal.span {(p : C)} := by
    rw [map_natCast]
  let e := Ideal.quotientEquivAlgOfEq C hI
  have hgCbase : IsSMulRegular (C ⧸ Ideal.span {algebraMap A C (p : A)})
      (algebraMap A C g) :=
    (isSMulRegular_algebraMap_iff (R := C)
      (A := C ⧸ Ideal.span {algebraMap A C (p : A)})).mp hgC'
  have hgC : IsSMulRegular (C ⧸ Ideal.span {(p : C)})
      (Ideal.Quotient.mk (Ideal.span {(p : C)}) (algebraMap A C g)) :=
    (isSMulRegular_algebraMap_iff (R := C) (A := C ⧸ Ideal.span {(p : C)})).mpr
      ((e.toLinearEquiv.isSMulRegular_congr (algebraMap A C g)).mp hgCbase)
  have haC := isSMulRegular_p_completedTower A t p ha
  let : IsAdicComplete (Ideal.span {(p : C)}) C := by
    rcases hperf with hsub | ⟨_, hc, _⟩
    · let : Subsingleton C := hsub
      infer_instance
    · exact hc
  constructor
  · have hh := isSMulRegular_quotient_span_of_regular_mod C
      (p : C) (algebraMap A C g) haC hgC
    have hcast : Ideal.Quotient.mk (Ideal.span {algebraMap A C g}) (p : C) =
        (p : C ⧸ Ideal.span {algebraMap A C g}) :=
      map_natCast (Ideal.Quotient.mk (Ideal.span {algebraMap A C g})) p
    rw [hcast] at hh
    exact hh
  · have hh := isAdicComplete_quotient_span_of_regular_mod C
      (p : C) (algebraMap A C g) haC hgC
    have hcast : Ideal.Quotient.mk (Ideal.span {algebraMap A C g}) (p : C) =
        (p : C ⧸ Ideal.span {algebraMap A C g}) :=
      map_natCast (Ideal.Quotient.mk (Ideal.span {algebraMap A C g})) p
    rw [hcast] at hh
    exact hh

theorem toPerfectoidization_cyclic_surjective_of_not_dvd
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {r : ℕ} (t : Fin (r + 2) → A) (p : ℕ) [Fact p.Prime]
    (ht : Ideal.span (Set.range t) = maximalIdeal A) (htp : t 0 = (p : A))
    (hdim : ringKrullDim A = r + 2) (hperf : IsIntegralPerfectoid (CompletedTower A t p) p)
    (g : A) (hpg : ¬ (p : A) ∣ g) :
    letI : Algebra.FinitePresentation (CompletedTower A t p)
        (CompletedTower A t p ⧸ Ideal.span {algebraMap A (CompletedTower A t p) g}) :=
      Algebra.FinitePresentation.quotient
        (Submodule.fg_span_singleton (algebraMap A (CompletedTower A t p) g))
    Function.Surjective (toQuotientPerfectoidization (CompletedTower A t p)
        (Ideal.span {algebraMap A (CompletedTower A t p) g}) p hperf) := by
  exact BhattScholze.perfectoidIdeal_quotientMap_surjective (CompletedTower A t p) p hperf
    (algebraMap A (CompletedTower A t p) g)

end SerrePositivity.CLMST
