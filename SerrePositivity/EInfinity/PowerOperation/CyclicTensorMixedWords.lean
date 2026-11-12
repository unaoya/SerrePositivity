module

public import SerrePositivity.EInfinity.PowerOperation.CyclicMixedOrbit
public import SerrePositivity.EInfinity.BarrattEccles.Theory.BinaryTensorColorAction

/-!
# 実際の二色テンソル語への巡回自由性の適用

DAG XIII Proposition 2.2.3 の混合項の補助。
以前の自由代数比較の入力語と同じ色付け・同じ置換作用を使う。
混合語の巡回軌道を、群の元そのもので忠実に添字付けする。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.EInfinity.PowerOperation
variable (p : ℕ) [NeZero p] [Fact p.Prime]

/-- 実際の混合二色語を固定する同じ巡回作用の群の元は単位。 -/
lemma cyclicBinaryTensorWord_fixed (w : BinaryTensorWord p)
    (hw : ∃ i j, binaryTensorWordColors p w i ≠ binaryTensorWordColors p w j)
    (g : PowerOperationCyclicGroup.{u} p)
    (hg : powerOperationCyclicPermutation p g • w = w) : g = 1 := by
  apply powerOperationCyclicPermutation_mixed_free p (binaryTensorWordColors p w) hw g
  intro i
  have h := congrArg
    (fun z => binaryTensorWordColors p z (powerOperationCyclicPermutation p g i)) hg
  simpa only [binaryTensorWordColors_smul, Equiv.symm_apply_apply] using h.symm

/-- 同じ混合入力語の巡回軌道は群の元で重複なく添字付けされる。 -/
lemma cyclicBinaryTensorWord_orbit_injective (w : BinaryTensorWord p)
    (hw : ∃ i j, binaryTensorWordColors p w i ≠ binaryTensorWordColors p w j) :
    Function.Injective (fun g : PowerOperationCyclicGroup.{u} p =>
      powerOperationCyclicPermutation p g • w) := by
  intro a b hab
  dsimp only at hab
  have h : powerOperationCyclicPermutation p (b⁻¹ * a) • w = w := by
    rw [map_mul, mul_smul, hab, map_inv, inv_smul_smul]
  have he := cyclicBinaryTensorWord_fixed p w hw (b⁻¹ * a) h
  exact (inv_mul_eq_one.mp he).symm

/-- 実際の混合入力語の軌道と巡回群との指定同値。 -/
def cyclicBinaryTensorWordOrbitEquiv (w : BinaryTensorWord p)
    (hw : ∃ i j, binaryTensorWordColors p w i ≠ binaryTensorWordColors p w j) :
    PowerOperationCyclicGroup.{u} p ≃
      Set.range (fun g : PowerOperationCyclicGroup.{u} p =>
        powerOperationCyclicPermutation p g • w) :=
  Equiv.ofInjective _ (cyclicBinaryTensorWord_orbit_injective p w hw)

end SerrePositivity.EInfinity.PowerOperation
