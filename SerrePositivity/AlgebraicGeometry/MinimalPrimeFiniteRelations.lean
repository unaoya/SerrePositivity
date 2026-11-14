module

public import Mathlib.RingTheory.KrullDimension.Zero
public import Mathlib.RingTheory.LocalProperties.Reduced
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Ideal.Maps

/-!
概要：被約環の極小素点の近くで有限個の関係を同時に消す。
方針：極小素点の局所環は体。局所化の零判定と有限積で分母をそろえる。
規約：基底環の Noether 性は不要。有限生成性を関係のイデアルにのみ仮定する。
使われ方：Rydh 3.10 の有限表示模型の係数を、極小素点の近傍で整域の模型へ移す。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
universe u
variable {R : Type u} [CommRing R] [IsReduced R]

/-- 被約環の極小素点に入る元は、その素点の外のある元により消える。 -/
theorem exists_annihilator_notMem_minimalPrime {p : Ideal R}
    (hp : p ∈ minimalPrimes R) {x : R} (hx : x ∈ p) :
    ∃ s : R, s ∉ p ∧ s * x = 0 := by
  have : p.IsPrime := hp.1.1
  have : Ring.KrullDimLE 0 (Localization.AtPrime p) := .of_isLocalization p hp _
  let : Field (Localization.AtPrime p) := Ring.KrullDimLE.isField_of_isReduced.toField
  have hz : algebraMap R (Localization.AtPrime p) x = 0 := by
    rw [← Ideal.mem_bot, ← IsLocalRing.maximalIdeal_eq_bot,
      ← Localization.AtPrime.map_eq_maximalIdeal]
    exact Ideal.mem_map_of_mem _ hx
  obtain ⟨s, hs⟩ := (IsLocalization.map_eq_zero_iff p.primeCompl
    (Localization.AtPrime p) x).mp hz
  exact ⟨s, s.property, hs⟩

/-- 同じ極小素点に入る有限個の元を、素点の外の一つの元で同時に消せる。 -/
theorem exists_common_annihilator_finset_minimalPrime {p : Ideal R}
    (hp : p ∈ minimalPrimes R) (S : Finset R) (hS : ∀ x ∈ S, x ∈ p) :
    ∃ s : R, s ∉ p ∧ ∀ x ∈ S, s * x = 0 := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, hp.1.1.one_notMem, by simp⟩
  | @insert a S ha ih =>
    obtain ⟨s, hs, hsa⟩ := exists_annihilator_notMem_minimalPrime hp (hS a (by simp))
    obtain ⟨t, ht, htS⟩ := ih (fun x hx ↦ hS x (Finset.mem_insert_of_mem hx))
    refine ⟨s * t, fun h ↦ (hp.1.1.mem_or_mem h).elim hs ht, ?_⟩
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · rw [mul_right_comm, hsa, zero_mul]
    · rw [mul_assoc, htS x hx, mul_zero]

/-- 有限生成イデアルが極小素点に入れば、その近傍でイデアル全体が消える。 -/
theorem exists_common_annihilator_fg_minimalPrime {p J : Ideal R}
    (hp : p ∈ minimalPrimes R) (hJ : J.FG) (hJp : J ≤ p) :
    ∃ s : R, s ∉ p ∧ ∀ x ∈ J, s * x = 0 := by
  obtain ⟨S, hS⟩ := hJ
  obtain ⟨s, hs, hsS⟩ := exists_common_annihilator_finset_minimalPrime hp S
    (fun x hx ↦ hJp (hS ▸ Ideal.subset_span hx))
  refine ⟨s, hs, ?_⟩
  have hann : s ∈ (Submodule.span R (S : Set R)).annihilator :=
    (Submodule.mem_annihilator_span _ _).mpr fun x ↦ hsS x.val x.property
  have heq : Submodule.span R (S : Set R) = J := hS
  rw [heq] at hann
  exact Submodule.mem_annihilator.mp hann

end SerrePositivity.AlgebraicGeometry
