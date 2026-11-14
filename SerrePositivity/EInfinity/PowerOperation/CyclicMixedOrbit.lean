module

public import SerrePositivity.EInfinity.PowerOperation.CyclicTensorInput
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

/-!
# p 入力の混合色の巡回軌道の自由性

DAG XIII Proposition 2.2.3 の Tate 正確性の証明に使う組合せ的な補助。
同じ指定巡回作用のもとで、非定数な色付けを固定する群の元は単位だけである。
色の型は二色に限定しない。ここではスペクトル的な Tate 消滅は主張しない。
-/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity.EInfinity.PowerOperation
variable (p : ℕ) [NeZero p]

/-- 同じ指定巡回作用は、p 個の入力に推移的に作用する。 -/
lemma powerOperationCyclicPermutation_transitive (i j : Fin p) :
    ∃ g : PowerOperationCyclicGroup.{u} p, powerOperationCyclicPermutation p g i = j := by
  refine ⟨ULift.up (Multiplicative.ofAdd (ZMod.finEquiv p j - ZMod.finEquiv p i)), ?_⟩
  simp [powerOperationCyclicPermutation]

/-- 同じ指定巡回作用で色付けを固定する部分群。 -/
def cyclicColorStabilizer {B : Type v} (w : Fin p → B) :
    Subgroup (PowerOperationCyclicGroup.{u} p) where
  carrier := {g | ∀ i, w (powerOperationCyclicPermutation p g i) = w i}
  one_mem' := by intro i; simp
  mul_mem' ha hb := by
    intro i
    simp only [Set.mem_ofPred_eq] at ha hb
    simpa only [map_mul, Equiv.Perm.mul_apply] using (ha _).trans (hb i)
  inv_mem' := by
    intro g hg i
    have h := hg (powerOperationCyclicPermutation p g⁻¹ i)
    simpa only [← Equiv.Perm.mul_apply, ← map_mul, mul_inv_cancel, map_one,
      Equiv.Perm.one_apply] using h.symm

/-- 素数位数では、非定数な色付けの同じ巡回安定化部分群は自明。 -/
lemma cyclicColorStabilizer_eq_bot [Fact p.Prime] {B : Type v} (w : Fin p → B)
    (hw : ∃ i j, w i ≠ w j) : cyclicColorStabilizer.{u} p w = ⊥ := by
  have hcard : Nat.card (PowerOperationCyclicGroup.{u} p) = p := by
    rw [Nat.card_eq_fintype_card]
    exact powerOperationCyclicGroup_card p
  have : Fact (Nat.card (PowerOperationCyclicGroup.{u} p)).Prime := ⟨hcard.symm ▸ Fact.out⟩
  rcases (cyclicColorStabilizer.{u} p w).eq_bot_or_eq_top_of_prime_card with h | h
  · exact h
  · obtain ⟨i, j, hij⟩ := hw
    obtain ⟨g, hg⟩ := powerOperationCyclicPermutation_transitive.{u} p i j
    have hm : g ∈ cyclicColorStabilizer p w := h.symm ▸ Subgroup.mem_top g
    exact (hij ((hm i).symm.trans (congrArg w hg))).elim

/-- 混合色を固定する巡回置換の群の元は単位だけ。 -/
lemma powerOperationCyclicPermutation_mixed_free [Fact p.Prime] {B : Type v}
    (w : Fin p → B) (hw : ∃ i j, w i ≠ w j) (g : PowerOperationCyclicGroup.{u} p)
    (hg : ∀ i, w (powerOperationCyclicPermutation p g i) = w i) : g = 1 := by
  have hm : g ∈ cyclicColorStabilizer p w := hg
  rw [cyclicColorStabilizer_eq_bot p w hw, Subgroup.mem_bot] at hm
  exact hm

end SerrePositivity.EInfinity.PowerOperation
