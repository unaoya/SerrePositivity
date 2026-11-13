module

public import SerrePositivity.EInfinity.PowerOperation.MayClosedCycles
public import SerrePositivity.EInfinity.PowerOperation.MayNormalization

/-!
# May の P⁰ の規格化された閉元

May, Definition 2.2 の P⁰：ホモロジー次数 n に対して ν(n)D_{−n(p−1)}。
p=2 では ν=1。負の係数次数は零とする。
ここでは閉元を作り、代表元独立性はまだ主張しない。
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded
open SerrePositivity.EInfinity.BarrattEccles
variable (p : ℕ) [Fact p.Prime]

/-- May の添字を使うと、指定 D_i の余鎖次数が −n に一致する。 -/
lemma mayPowerZero_degree (n : ℤ) (hn : 0 ≤ mayZeroIndex p n) :
    -((mayZeroIndex p n).toNat : ℤ) + mayRepeatedDegree (-n) p = -n := by
  rw [Int.toNat_of_nonneg hn, mayRepeatedDegree_eq, mul_neg]
  have h := congrArg Neg.neg (mayZeroIndex_degree p n)
  simpa only [neg_add, add_comm] using h

/-- 同じ指定係数による P⁰ の、全整数次数の規格化された閉元。 -/
def mayPowerZeroCycle (X : (operad (ZMod p)).Algebra) (n : ℤ)
    (a : MayClosed X.carrier (-n)) : MayClosed X.carrier (-n) :=
  if hn : 0 ≤ mayZeroIndex p n then
    (mayNu p n : ZMod p) • mayClosedIndex X.carrier (mayPowerZero_degree p n hn)
      (mayDClosed X p (mayZeroIndex p n).toNat (-n) a)
  else 0

/-- 正のホモトピー次数では、係数の添字が負なので指定閉元は零。 -/
lemma mayPowerZeroCycle_pos (X : (operad (ZMod p)).Algebra) (n : ℤ) (hn : 0 < n)
    (a : MayClosed X.carrier (-n)) : mayPowerZeroCycle p X n a = 0 := by
  simp only [mayPowerZeroCycle, not_le.mpr (mayZeroIndex_negative p hn), dite_false]

/-- 規格化と次数の移送を含む同じ閉元は、全厳密 BE 射に自然。 -/
lemma mayPowerZeroCycle_naturality {X Y : (operad (ZMod p)).Algebra} (f : X ⟶ Y)
    (n : ℤ) (a : MayClosed X.carrier (-n)) :
    mayClosedMap f.hom (-n) (mayPowerZeroCycle p X n a) =
      mayPowerZeroCycle p Y n (mayClosedMap f.hom (-n) a) := by
  unfold mayPowerZeroCycle
  split_ifs with hn
  · rw [map_smul, mayClosedMap_index, mayDClosed_naturality]
  · exact (mayClosedMap f.hom (-n)).map_zero

end SerrePositivity.EInfinity.PowerOperation
