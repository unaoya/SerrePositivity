module

public import SerrePositivity.EInfinity.PowerOperation.MayDClassAdditivity
public import SerrePositivity.EInfinity.PowerOperation.MayPowerZeroClasses

/-!
# May の P⁰ の加法性

May, Proposition 2.3(ii)。指定 D_i の加法性を規格化と次数移送の後に使い、
代表元に依存しない P⁰ を可換群の準同型として束ねる。
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory HomologicalComplex
open SerrePositivity.EInfinity.BarrattEccles
variable (p : ℕ) [Fact p.Prime] (X : (operad (ZMod p)).Algebra)

lemma mayPowerZeroClass_add (n : ℤ) (a b : MayClosed X.carrier (-n)) :
    mayPowerZeroClass p X n (a + b) =
      mayPowerZeroClass p X n a + mayPowerZeroClass p X n b := by
  unfold mayPowerZeroClass mayPowerZeroCycle
  split_ifs with hn
  · rw [map_smul, map_smul, map_smul, mayClosedClass_index,
      mayClosedClass_index, mayClosedClass_index]
    have hadd := mayDClass_add p X (mayZeroIndex p n).toNat (-n) a b
    unfold mayDClass at hadd
    rw [hadd, map_add, smul_add]
  · simp only [map_zero, add_zero]

lemma mayPowerZeroHomology_add (n : ℤ) (x y : X.carrier.homology (-n)) :
    mayPowerZeroHomology p X n (x + y) =
      mayPowerZeroHomology p X n x + mayPowerZeroHomology p X n y := by
  obtain ⟨a, rfl⟩ := mayClosedClass_surjective X.carrier (-n) x
  obtain ⟨b, rfl⟩ := mayClosedClass_surjective X.carrier (-n) y
  rw [← map_add, mayPowerZeroHomology_class, mayPowerZeroHomology_class,
    mayPowerZeroHomology_class, mayPowerZeroClass_add]

/-- 全整数次数での、実ホモロジーの可換群上の May の P⁰。 -/
def mayPowerZeroAddHom (n : ℤ) : X.carrier.homology (-n) →+ X.carrier.homology (-n) :=
  AddMonoidHom.mk' (mayPowerZeroHomology p X n) (mayPowerZeroHomology_add p X n)

lemma mayPowerZeroAddHom_apply (n : ℤ) (x : X.carrier.homology (-n)) :
    mayPowerZeroAddHom p X n x = mayPowerZeroHomology p X n x := rfl

lemma mayPowerZeroAddHom_naturality {Y : (operad (ZMod p)).Algebra} (f : X ⟶ Y)
    (n : ℤ) (x : X.carrier.homology (-n)) :
    homologyMap f.hom (-n) (mayPowerZeroAddHom p X n x) =
      mayPowerZeroAddHom p Y n (homologyMap f.hom (-n) x) :=
  mayPowerZeroHomology_naturality p X f n x

end SerrePositivity.EInfinity.PowerOperation
