module

public import SerrePositivity.EInfinity.PowerOperation.MayCyclicGroup
public import SerrePositivity.EInfinity.PowerOperation.CyclicTensorMixedWords
public import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# May の混合二色語の実巡回軌道

May, Proposition 2.3(ii) のノルム表示の組合せ的な前段。
既存の混合語の自由性を同じ実巡回部分群へ移し、各軌道を群で一度ずつ列挙する。
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
variable (p : ℕ) [NeZero p]

/-- 二つの色がともに現れる、既存の入力語。 -/
abbrev MayMixedWord := {w : BinaryTensorWord p //
  ∃ i j, binaryTensorWordColors p w i ≠ binaryTensorWordColors p w j}

instance mayMixedWordFintype : Fintype (MayMixedWord p) := Fintype.ofFinite _

/-- 実巡回部分群の作用は混合語を保つ。 -/
instance mayMixedWordMulAction : MulAction (MayCyclicGroup.{u} p) (MayMixedWord p) where
  smul g w := ⟨g.val.down • w.val, by
    obtain ⟨i, j, hij⟩ := w.property
    refine ⟨g.val.down i, g.val.down j, ?_⟩
    simpa only [binaryTensorWordColors_smul, Equiv.symm_apply_apply] using hij⟩
  one_smul w := by
    apply Subtype.ext
    change (1 : Equiv.Perm (Fin p)) • w.val = w.val
    exact one_smul _ _
  mul_smul g h w := by
    apply Subtype.ext
    change (g.val.down * h.val.down) • w.val = g.val.down • (h.val.down • w.val)
    exact mul_smul _ _ _

lemma mayMixedWord_smul_val (g : MayCyclicGroup.{u} p) (w : MayMixedWord p) :
    (g • w).val = g.val.down • w.val := rfl

/-- 元の Z/p 表示と、同じ実部分群の置換は一致する。 -/
lemma mayCyclicGroupEquiv_permutation (g : MayCyclicGroup.{u} p) :
    powerOperationCyclicPermutation p ((mayCyclicGroupEquiv p).symm g) = g.val.down := by
  have h := congrArg (fun h : MayCyclicGroup.{u} p => h.val.down)
    ((mayCyclicGroupEquiv p).apply_symm_apply g)
  exact h

variable [Fact p.Prime]

/-- 同じ実部分群の混合語の作用は自由。 -/
lemma mayMixedWord_fixed (g : MayCyclicGroup.{u} p) (w : MayMixedWord p)
    (h : g • w = w) : g = 1 := by
  have hw := congrArg Subtype.val h
  change g.val.down • w.val = w.val at hw
  rw [← mayCyclicGroupEquiv_permutation p g] at hw
  have he := cyclicBinaryTensorWord_fixed p w.val w.property _ hw
  have hm := congrArg (mayCyclicGroupEquiv p) he
  simpa only [MulEquiv.apply_symm_apply, map_one] using hm

lemma mayMixedWord_orbit_injective (w : MayMixedWord p) :
    Function.Injective (fun g : MayCyclicGroup.{u} p => g • w) := by
  intro g h hgh
  dsimp only at hgh
  have he : (h⁻¹ * g) • w = w := by rw [mul_smul, hgh, inv_smul_smul]
  exact (inv_mul_eq_one.mp (mayMixedWord_fixed p _ w he)).symm

/-- 各混合軌道の重複のない、指定された実巡回群による列挙。 -/
def mayMixedWordOrbitEquiv (w : MayMixedWord p) :
    MayCyclicGroup.{u} p ≃ MulAction.orbit (MayCyclicGroup.{u} p) w :=
  Equiv.ofInjective _ (mayMixedWord_orbit_injective p w)

/-- 同じ実巡回作用の混合軌道の集合。 -/
abbrev MayMixedOrbit := MulAction.orbitRel.Quotient (MayCyclicGroup.{u} p) (MayMixedWord p)

instance mayMixedOrbitFintype : Fintype (MayMixedOrbit.{u} p) := Fintype.ofFinite _

/-- 混合語を軌道と、その軌道の代表を動かす群の元で一度ずつ表す。 -/
def mayMixedWordSigmaEquiv :
    MayMixedWord p ≃ Σ _ : MayMixedOrbit.{u} p, MayCyclicGroup.{u} p :=
  (MulAction.selfEquivSigmaOrbits (MayCyclicGroup.{u} p) (MayMixedWord p)).trans
    (Equiv.sigmaCongrRight fun ω => (mayMixedWordOrbitEquiv p ω.out).symm)

lemma mayMixedWordSigmaEquiv_symm_apply (ω : MayMixedOrbit.{u} p)
    (g : MayCyclicGroup.{u} p) :
    (mayMixedWordSigmaEquiv p).symm ⟨ω, g⟩ = g • ω.out := by
  rfl

/-- 混合語の全和を、各軌道の代表のノルムの和として表す。 -/
lemma mayMixedWord_sum_orbits {A : Type*} [AddCommMonoid A] (f : MayMixedWord p → A) :
    ∑ w : MayMixedWord p, f w =
      ∑ ω : MayMixedOrbit.{u} p, ∑ g : MayCyclicGroup.{u} p, f (g • ω.out) := by
  have h := Equiv.sum_comp (mayMixedWordSigmaEquiv.{u} p).symm f
  rw [Fintype.sum_sigma] at h
  simpa only [mayMixedWordSigmaEquiv_symm_apply] using h.symm

end SerrePositivity.EInfinity.PowerOperation
