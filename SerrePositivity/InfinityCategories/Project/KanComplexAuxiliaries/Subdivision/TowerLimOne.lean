module


public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Hom.Basic

/-!
概要：群の逆向きの塔の非可換 lim¹ と、全射な遷移のときの消滅。
方針：積の群の twisted 作用の軌道を商とし、前段の解を順次持ち上げる。
規約：一般の場合は基点付き集合。ホモトピー群の比較の核との同定は別工程。
使われ方：Goerss–Jardine VIII §1。Milnor の lim¹ の代数的な項。
-/

@[expose] public section
universe u

namespace SerrePositivity.KST.Spectra.TowerLimOne
end SerrePositivity.KST.Spectra.TowerLimOne
namespace SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TowerLimOne
open _root_.SerrePositivity.KST.Spectra
open _root_.SerrePositivity.KST.Spectra.TowerLimOne

noncomputable section

variable (G : ℕ → Type u) [∀ n, Group (G n)] (q : ∀ n, G (n + 1) →* G n)

/-- 積の群による、塔の遷移を組み込んだ twisted 作用。 -/
def twist (a x : ∀ n, G n) (n : ℕ) : G n := a n * x n * (q n (a (n + 1)))⁻¹

/-- 単位族の twisted 作用は恒等。 -/
lemma twist_one (x : ∀ n, G n) : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TowerLimOne.twist G q 1 x = x := by
  funext n
  simp [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TowerLimOne.twist]

/-- twisted 作用は積の群の左作用。 -/
lemma twist_mul (a b x : ∀ n, G n) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TowerLimOne.twist G q (a * b) x = _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TowerLimOne.twist G q a (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TowerLimOne.twist G q b x) := by
  funext n
  simp only [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TowerLimOne.twist, Pi.mul_apply, map_mul, mul_inv_rev, mul_assoc]

/-- lim¹ の軌道関係。逆元と合成により同値関係になる。 -/
def orbitSetoid : Setoid (∀ n, G n) where
  r x y := ∃ a, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TowerLimOne.twist G q a x = y
  iseqv := {
    refl x := ⟨1, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TowerLimOne.twist_one G q x⟩
    symm := by
      rintro x y ⟨a, ha⟩
      refine ⟨a⁻¹, ?_⟩
      rw [← ha, ← _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TowerLimOne.twist_mul, inv_mul_cancel, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TowerLimOne.twist_one]
    trans := by
      rintro x y z ⟨a, ha⟩ ⟨b, hb⟩
      exact ⟨b * a, (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TowerLimOne.twist_mul G q b a x).trans
        ((congrArg (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TowerLimOne.twist G q b) ha).trans hb)⟩ }

/-- 非可換な群の塔の第一導来逆極限の基点付き集合。 -/
def limOne : Type u := Quotient (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TowerLimOne.orbitSetoid G q)

/-- 積の群の族を lim¹ の軌道へ送る標準射。 -/
def mk (x : ∀ n, G n) : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TowerLimOne.limOne G q := Quotient.mk _ x

/-- 単位族の軌道が lim¹ の標準基点。 -/
def point : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TowerLimOne.limOne G q := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TowerLimOne.mk G q 1

/-- 同じ twisted 軌道の族は lim¹ で同じ元。 -/
lemma mk_twist (a x : ∀ n, G n) : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TowerLimOne.mk G q x = _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TowerLimOne.mk G q (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TowerLimOne.twist G q a x) :=
  Quotient.sound ⟨a, rfl⟩

/-- 全射な遷移の下で、指定した族を単位軌道へ送る作用の族を逐次選ぶ。 -/
def nullifier (hq : ∀ n, Function.Surjective (q n)) (x : ∀ n, G n) : ∀ n, G n
  | 0 => 1
  | n + 1 => Classical.choose (hq n (nullifier hq x n * x n))

/-- 選んだ次段の作用の射影は、前段の方程式を満たす。 -/
lemma nullifier_projection (hq : ∀ n, Function.Surjective (q n)) (x : ∀ n, G n) (n : ℕ) :
    q n (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TowerLimOne.nullifier G q hq x (n + 1)) = _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TowerLimOne.nullifier G q hq x n * x n :=
  Classical.choose_spec (hq n (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TowerLimOne.nullifier G q hq x n * x n))

/-- 全射な遷移では、任意の族を単位族へ送る twisted 作用がある。 -/
lemma twist_nullifier (hq : ∀ n, Function.Surjective (q n)) (x : ∀ n, G n) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TowerLimOne.twist G q (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TowerLimOne.nullifier G q hq x) x = 1 := by
  funext n
  rw [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TowerLimOne.twist, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TowerLimOne.nullifier_projection, mul_inv_cancel]
  rfl

/-- 全射な遷移の塔の lim¹ は標準基点だけからなる。 -/
lemma mk_eq_point (hq : ∀ n, Function.Surjective (q n)) (x : ∀ n, G n) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TowerLimOne.mk G q x = _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TowerLimOne.point G q :=
  Quotient.sound ⟨_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TowerLimOne.nullifier G q hq x, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TowerLimOne.twist_nullifier G q hq x⟩

/-- 全射な遷移の塔の非可換 lim¹ の消滅。 -/
theorem subsingleton_of_surjective (hq : ∀ n, Function.Surjective (q n)) :
    Subsingleton (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TowerLimOne.limOne G q) := by
  constructor
  intro a b
  induction a using Quotient.inductionOn with | h x => ?_
  induction b using Quotient.inductionOn with | h y => ?_
  exact (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TowerLimOne.mk_eq_point G q hq x).trans (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TowerLimOne.mk_eq_point G q hq y).symm

end
end SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TowerLimOne

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
