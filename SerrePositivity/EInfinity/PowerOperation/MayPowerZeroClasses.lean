module

public import SerrePositivity.EInfinity.PowerOperation.MayDClasses
public import SerrePositivity.EInfinity.PowerOperation.MayPowerZeroCycles

/-!
# May の P⁰ のホモロジー上の値

May, Definition 2.2・Proposition 2.3 の規格化と代表元独立性。
ここでは全整数次数でホモロジーの上の関数を作る。
可換群の準同型として束ねるには、加法性を別に証明する。
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded
open SerrePositivity.EInfinity.BarrattEccles
variable (p : ℕ) [Fact p.Prime] (X : (operad (ZMod p)).Algebra)

/-- 同じ規格化された P⁰ の閉元の実ホモロジー類。 -/
def mayPowerZeroClass (n : ℤ) (a : MayClosed X.carrier (-n)) : X.carrier.homology (-n) :=
  mayClosedClass X.carrier (-n) (mayPowerZeroCycle p X n a)

lemma mayPowerZeroClass_independent (n : ℤ) (a b : MayClosed X.carrier (-n))
    (hab : mayClosedClass X.carrier (-n) a = mayClosedClass X.carrier (-n) b) :
    mayPowerZeroClass p X n a = mayPowerZeroClass p X n b := by
  unfold mayPowerZeroClass mayPowerZeroCycle
  split_ifs with hn
  · rw [map_smul, map_smul, mayClosedClass_index, mayClosedClass_index]
    exact congrArg
      (fun x => (mayNu p n : ZMod p) •
        (eqToHom (congrArg (fun i : ℤ => X.carrier.homology i) (mayPowerZero_degree p n hn))).hom x)
      (mayDClass_independent p X (mayZeroIndex p n).toNat (-n) a b hab)
  · rfl

lemma mayPowerZeroClass_naturality {Y : (operad (ZMod p)).Algebra} (f : X ⟶ Y)
    (n : ℤ) (a : MayClosed X.carrier (-n)) :
    homologyMap f.hom (-n) (mayPowerZeroClass p X n a) =
      mayPowerZeroClass p Y n (mayClosedMap f.hom (-n) a) := by
  rw [mayPowerZeroClass, mayClosedClass_naturality, mayPowerZeroCycle_naturality]
  rfl

/-- 同じ P⁰ を実ホモロジーの元へ降ろした関数。加法性は後で示す。 -/
def mayPowerZeroHomology (n : ℤ) (x : X.carrier.homology (-n)) : X.carrier.homology (-n) :=
  mayPowerZeroClass p X n (mayClosedRepresentative X.carrier (-n) x)

lemma mayPowerZeroHomology_class (n : ℤ) (a : MayClosed X.carrier (-n)) :
    mayPowerZeroHomology p X n (mayClosedClass X.carrier (-n) a) =
      mayPowerZeroClass p X n a := by
  apply mayPowerZeroClass_independent
  exact mayClosedRepresentative_spec X.carrier (-n) _

lemma mayPowerZeroHomology_pos (n : ℤ) (hn : 0 < n) (x : X.carrier.homology (-n)) :
    mayPowerZeroHomology p X n x = 0 := by
  unfold mayPowerZeroHomology mayPowerZeroClass
  rw [mayPowerZeroCycle_pos p X n hn, map_zero]

/-- 選んだ代表への依存を消した後の、全厳密 BE 射での自然性。 -/
lemma mayPowerZeroHomology_naturality {Y : (operad (ZMod p)).Algebra} (f : X ⟶ Y)
    (n : ℤ) (x : X.carrier.homology (-n)) :
    homologyMap f.hom (-n) (mayPowerZeroHomology p X n x) =
      mayPowerZeroHomology p Y n (homologyMap f.hom (-n) x) := by
  let a := mayClosedRepresentative X.carrier (-n) x
  have ha : mayClosedClass X.carrier (-n) a = x := mayClosedRepresentative_spec X.carrier (-n) x
  rw [← ha, mayPowerZeroHomology_class, mayPowerZeroClass_naturality,
    mayClosedClass_naturality, mayPowerZeroHomology_class]

end SerrePositivity.EInfinity.PowerOperation
