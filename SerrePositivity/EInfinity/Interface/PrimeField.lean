module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Field.ULift

/-!
# 冪作用の本欄に使う素体

May, Definition 2.2・Proposition 2.3 の P⁰ を F_p に限って受け取る。
界面の基底環は Type u にあるので、同じ F_p を ULift して置く。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.EInfinity

/-- 界面の宇宙に置いた F_p。一般の標数 p の環を本欄に追加するものではない。 -/
abbrev EInfinityPrimeField (p : ℕ) := ULift.{u} (ZMod p)

/-- F_p の同じ元を、宇宙を持ち上げた素体に置く環同型。 -/
def eInfinityPrimeFieldEquiv (p : ℕ) : EInfinityPrimeField.{u} p ≃+* ZMod p :=
  ULift.ringEquiv

end SerrePositivity.EInfinity
