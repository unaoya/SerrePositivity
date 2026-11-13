module

public import SerrePositivity.EInfinity.PowerOperation.MayPureMixedWords
public import SerrePositivity.EInfinity.PowerOperation.MayColoredCyclic

/-!
# May の混合入力のノルム表示

May, Proposition 2.3(ii) の Δ(a,b)=Nc。
同じ実巡回群と同じ二色語の軌道代表を使い、実テンソル複体でノルムを計算する。
ここでのノルムは有限個の線形射の和であり、スペクトルのノルムは使わない。
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers
variable {k : Type u} [CommRing k] (p : ℕ) [NeZero p]

/-- 元のテンソル冪の同じ次数上の、実巡回群の作用の有限和。 -/
def mayInputNorm (K : Complex k) (q : ℤ) :
    (power K p).X (mayRepeatedDegree q p) →ₗ[k] (power K p).X (mayRepeatedDegree q p) :=
  ∑ g : MayCyclicGroup.{u} p,
    ((permutationAction K p g.val.down).asIso.hom.f (mayRepeatedDegree q p)).hom

variable [Fact p.Prime]

/-- 各混合軌道から同じ代表を一つずつ選んだ同次テンソルの和。 -/
def mayMixedInputRepresentative (K : Complex k) (q : ℤ) (a b : K.X q) :
    (power K p).X (mayRepeatedDegree q p) :=
  ∑ ω : MayMixedOrbit.{u} p, mayColoredValue K q a b p ω.out.val

omit [Fact p.Prime] in
lemma mayMixedInputRepresentative_cycle (K : Complex k) (q : ℤ) (a b : K.X q)
    (ha : K.d q (q + 1) a = 0) (hb : K.d q (q + 1) b = 0) :
    (power K p).d (mayRepeatedDegree q p) (mayRepeatedDegree q p + 1)
      (mayMixedInputRepresentative p K q a b) = 0 := by
  change ((power K p).d _ _).hom (∑ ω : MayMixedOrbit.{u} p, _) = 0
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro ω hω
  exact mayColoredValue_cycle K q a b ha hb p ω.out.val

/-- 二項展開の混合差は、選んだ同じ混合代表のノルムに一致する。 -/
lemma mayMixedInputRepresentative_norm [CharP k p]
    (K : Complex k) (q : ℤ) (a b : K.X q) :
    mayInputNorm p K q (mayMixedInputRepresentative p K q a b) =
      mayRepeatedValue K q (a + b) p - mayRepeatedValue K q a p - mayRepeatedValue K q b p := by
  have hs := mayMixedWord_sum_orbits.{u} p (fun w => mayColoredValue K q a b p w.val)
  rw [← mayColoredValue_mixed_sum] at hs
  change mayInputNorm p K q (∑ ω : MayMixedOrbit.{u} p, _) = _
  rw [map_sum]
  calc
    _ = ∑ ω : MayMixedOrbit.{u} p,
        ∑ g : MayCyclicGroup.{u} p, mayColoredValue K q a b p (g • ω.out).val := by
      apply Finset.sum_congr rfl
      intro ω hω
      rw [mayInputNorm, LinearMap.sum_apply]
      apply Finset.sum_congr rfl
      intro g hg
      exact mayColoredValue_cyclic p K q a b g ω.out.val
    _ = _ := hs.symm

end SerrePositivity.EInfinity.PowerOperation
