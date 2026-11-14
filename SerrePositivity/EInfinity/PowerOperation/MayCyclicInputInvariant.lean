module

public import SerrePositivity.EInfinity.PowerOperation.MayRepeatedPermutation
public import SerrePositivity.EInfinity.PowerOperation.MayCyclicGroup
public import Mathlib.Algebra.CharP.Lemmas

/-!
# May の反復入力の巡回不変性

May, Definition 2.1 の巡回平衡関係の入力側。
奇素数では巡回置換は偶置換であり、標数 2 では全 Koszul 符号が消える。
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers
variable (p : ℕ) [NeZero p]

lemma mayCyclicSign_pow (g : MayCyclicGroup.{u} p) :
    Equiv.Perm.sign g.val.down ^ p = 1 := by
  have hg : g ^ p = 1 := by
    simpa only [mayCyclicGroup_card] using (pow_card_eq_one (x := g))
  have h := congrArg (fun h : MayCyclicGroup.{u} p => Equiv.Perm.sign h.val.down) hg
  change Equiv.Perm.sign (g.val.down ^ p) = Equiv.Perm.sign (1 : Equiv.Perm (Fin p)) at h
  simpa only [map_pow, map_one] using h

/-- 奇数位数の巡回置換は、同じ実対称群で偶置換である。 -/
lemma mayCyclicSign_odd (hp : Odd p) (g : MayCyclicGroup.{u} p) :
    Equiv.Perm.sign g.val.down = 1 := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign g.val.down) with he | he
  · exact he
  · have h := mayCyclicSign_pow p g
    rw [he, hp.neg_one_pow] at h
    have hv := congrArg Units.val h
    norm_num at hv

/-- 標数 2 の加群では、どの整数単元も恒等に作用する。 -/
lemma mayIntegerUnit_smul_charTwo {k : Type u} [CommRing k] [CharP k 2]
    {M : Type u} [AddCommGroup M] [Module k M] (v : ℤˣ) (x : M) : v • x = x := by
  rcases Int.units_eq_one_or v with hv | hv
  · rw [hv, one_smul]
  · rw [hv, Units.smul_def, Units.val_neg, Units.val_one, neg_one_smul]
    have hz : (2 : k) = 0 := CharP.cast_eq_zero k 2
    have ht : (2 : k) • x = 0 := by rw [hz, zero_smul]
    have ha : x + x = 0 := by simpa only [two_smul] using ht
    exact neg_eq_of_add_eq_zero_left ha

/-- 同じ同次入力の p 重反復は、標数 p の全巡回部分群で不変。 -/
lemma mayRepeatedValue_cyclic {k : Type u} [CommRing k] [Fact p.Prime] [CharP k p]
    (K : Complex k) (q : ℤ) (a : K.X q) (g : MayCyclicGroup.{u} p) :
    (permutationAction K p g.val.down).asIso.hom.f (mayRepeatedDegree q p)
      (mayRepeatedValue K q a p) = mayRepeatedValue K q a p := by
  rw [mayRepeatedValue_permutation]
  rcases (Fact.out : p.Prime).eq_two_or_odd' with hp | hp
  · subst p
    exact mayIntegerUnit_smul_charTwo (k := k) _ _
  · rw [mayCyclicSign_odd p hp g, one_zpow, one_smul]

end SerrePositivity.EInfinity.PowerOperation
