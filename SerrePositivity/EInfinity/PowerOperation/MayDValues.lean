module

public import SerrePositivity.EInfinity.PowerOperation.MayCoefficientAction
public import SerrePositivity.EInfinity.PowerOperation.MayCyclicInputInvariant

/-!
# May の指定 D_i の同次値と閉性

May, Definitions 2.1・2.2 の θ(e_i ⊗ a^{⊗p})。
同じ W→BE 比較を使い、標数 p で閉入力から閉元を作る。
代表元独立性と加法性は、この段階の閉性とは別に証明する。
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers
open SerrePositivity.EInfinity.BarrattEccles
variable {k : Type u} [CommRing k] (X : (operad k).Algebra)
variable (p : ℕ) [NeZero p]

/-- May の同じ e_s と同じ同次入力の反復を、元の BE 作用で評価する。 -/
def mayDValue (s : ℕ) (q : ℤ) (a : X.carrier.X q) :
    X.carrier.X (-(s : ℤ) + mayRepeatedDegree q p) :=
  mayHomogeneousAction X p (-(s : ℤ)) (mayRepeatedDegree q p)
    (mayActualCoefficient p s (mayCoefficientValue p k s))
    (mayRepeatedValue X.carrier q a p)

/-- 指定 D_s の同次値は、全厳密 BE 射について自然。 -/
lemma mayDValue_naturality {Y : (operad k).Algebra} (f : X ⟶ Y)
    (s : ℕ) (q : ℤ) (a : X.carrier.X q) :
    f.hom.f (-(s : ℤ) + mayRepeatedDegree q p) (mayDValue X p s q a) =
      mayDValue Y p s q (f.hom.f q a) := by
  rw [mayDValue, mayHomogeneousAction_naturality, mayRepeatedValue_naturality]
  rfl

/-- May の指定 D_s は、閉入力に対して実際の複体の閉元を与える。 -/
lemma mayDValue_cycle [Fact p.Prime] [CharP k p]
    (s : ℕ) (q : ℤ) (a : X.carrier.X q) (ha : X.carrier.d q (q + 1) a = 0) :
    X.carrier.d (-(s : ℤ) + mayRepeatedDegree q p)
      (-(s : ℤ) + mayRepeatedDegree q p + 1) (mayDValue X p s q a) = 0 := by
  have hy := mayRepeatedValue_cycle X.carrier q a ha p
  cases s with
  | zero =>
    have hc : ((operad k).arity p).d 0 1
        (mayActualCoefficient p 0 (mayCoefficientValue p k 0)) = 0 := by
      have h := (mayZeroCoefficientCycle p k).property
      exact LinearMap.mem_ker.mp h
    change X.carrier.d (0 + mayRepeatedDegree q p) (0 + mayRepeatedDegree q p + 1)
      (mayHomogeneousAction X p 0 (mayRepeatedDegree q p) _ _) = 0
    apply mayHomogeneousAction_cycle X p 0 (mayRepeatedDegree q p) _ _ hy
    have h := congrArg
      (fun z : ((operad k).arity p).X 1 =>
        mayHomogeneousAction X p 1 (mayRepeatedDegree q p) z
          (mayRepeatedValue X.carrier q a p)) hc
    exact h.trans ((mayHomogeneousActionLinear X p 1 (mayRepeatedDegree q p)).flip
      (mayRepeatedValue X.carrier q a p)).map_zero
  | succ s =>
    have hb : mayHomogeneousAction X p (-((s + 1 : ℕ) : ℤ) + 1)
        (mayRepeatedDegree q p)
        (((operad k).arity p).d (-((s + 1 : ℕ) : ℤ)) (-((s + 1 : ℕ) : ℤ) + 1)
          (mayActualCoefficient p (s + 1) (mayCoefficientValue p k (s + 1))))
        (mayRepeatedValue X.carrier q a p) = 0 := by
      generalize ht : -((s + 1 : ℕ) : ℤ) + 1 = t
      have ht' : t = -(s : ℤ) := by push_cast at ht; omega
      clear ht
      subst t
      exact mayCoefficientAction_boundary_zero X p s (mayRepeatedDegree q p)
        (mayRepeatedValue X.carrier q a p) (mayRepeatedValue_cyclic p X.carrier q a)
    exact mayHomogeneousAction_cycle X p _ _ _ _ hy hb

end SerrePositivity.EInfinity.PowerOperation
