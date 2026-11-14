module

public import SerrePositivity.EInfinity.PowerOperation.MayCyclicGroup
public import SerrePositivity.EInfinity.PowerOperation.MayNormPolynomial
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
public import Mathlib.RepresentationTheory.Basic

/-!
# May の同じ巡回生成元の差とノルム

May, Proposition 2.3(ii) の T^{p−1}=N。
実部分群の同じ指定生成元の冪で全群を一度ずつ列挙し、係数恒等式を表現に評価する。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.EInfinity.PowerOperation
variable (p : ℕ) [NeZero p]

lemma mayCyclicGenerator_order : orderOf (mayCyclicGenerator.{u} p) = p := by
  rw [orderOf_eq_card_of_forall_mem_zpowers (mayCyclicGenerator_generates p),
    Nat.card_eq_fintype_card, mayCyclicGroup_card]

/-- 指定生成元の 0,…,p−1 乗による、同じ実巡回群の重複のない列挙。 -/
def mayCyclicPowerEquiv : Fin p ≃ MayCyclicGroup.{u} p := by
  classical
  apply Equiv.ofBijective (fun i : Fin p => mayCyclicGenerator p ^ (i : ℕ))
  constructor
  · intro i j hij
    apply Fin.ext
    exact pow_injOn_Iio_orderOf
      (by change (i : ℕ) < orderOf (mayCyclicGenerator p)
          rw [mayCyclicGenerator_order]; exact i.isLt)
      (by change (j : ℕ) < orderOf (mayCyclicGenerator p)
          rw [mayCyclicGenerator_order]; exact j.isLt) hij
  · intro g
    have hg := mayCyclicGenerator_generates p g
    rw [mem_zpowers_iff_mem_range_orderOf, mayCyclicGenerator_order] at hg
    obtain ⟨i, hi, hgi⟩ := Finset.mem_image.mp hg
    exact ⟨⟨i, Finset.mem_range.mp hi⟩, hgi⟩

lemma mayCyclicPowerEquiv_apply (i : Fin p) :
    mayCyclicPowerEquiv.{u} p i = mayCyclicGenerator p ^ (i : ℕ) := rfl

/-- 同じ実巡回群の表現では、指定生成元の差の p−1 乗がノルム。 -/
lemma mayCyclicNorm_eq [Fact p.Prime] {V : Type u} [AddCommGroup V] [Module (ZMod p) V]
    (ρ : Representation (ZMod p) (MayCyclicGroup.{u} p) V) :
    ρ.norm = (ρ (mayCyclicGenerator p) - 1) ^ (p - 1) := by
  calc
    ρ.norm = ∑ i : Fin p, ρ (mayCyclicGenerator p ^ (i : ℕ)) := by
      exact (Equiv.sum_comp (mayCyclicPowerEquiv p) (fun g => ρ g)).symm
    _ = ∑ i ∈ Finset.range p, ρ (mayCyclicGenerator p) ^ i := by
      simp only [map_pow, Fin.sum_univ_eq_sum_range]
    _ = (ρ (mayCyclicGenerator p) - 1) ^ (p - 1) :=
      (mayNormPolynomial_aeval p (ρ (mayCyclicGenerator p))).symm

end SerrePositivity.EInfinity.PowerOperation
