module
public import SerrePositivity.KST.SConstruction.CutSegalEquivalence

/-! # 空でない有限個の単体集合の積
概要：同じ単体集合の正の有限個の積と元の各成分への射影・射対を構成する。
方針：右結合の Cartesian tensor を再帰し、射対の合成と射影を帰納で照合する。
規約：n は n+1 個の因子を表す。使われ方：全辺の Segal 射の明示的な標的。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet

/-- n+1 個の同じ単体集合の右結合の積。 -/
def nonemptySSetPower (A : SSet.{u}) : ℕ → SSet.{u}
  | 0 => A
  | n + 1 => A ⊗ nonemptySSetPower A n

/-- 正の有限積の元の各因子への射影。 -/
def nonemptySSetPowerProjection (A : SSet.{u}) :
    (n : ℕ) → Fin (n + 1) → (nonemptySSetPower A n ⟶ A)
  | 0, _ => 𝟙 A
  | n + 1, i => Fin.cases (CartesianMonoidalCategory.fst _ _)
      (fun j => CartesianMonoidalCategory.snd _ _ ≫ nonemptySSetPowerProjection A n j) i

/-- n+1 個の射から正の有限積への標準の射を作る。 -/
def nonemptySSetPowerLift {T A : SSet.{u}} :
    (n : ℕ) → (Fin (n + 1) → (T ⟶ A)) → (T ⟶ nonemptySSetPower A n)
  | 0, f => f 0
  | n + 1, f => CartesianMonoidalCategory.lift (f 0)
      (nonemptySSetPowerLift n (fun j => f j.succ))

/-- 正の有限積への標準の射の各成分は元の射。 -/
lemma nonemptySSetPowerLift_projection {T A : SSet.{u}} (n : ℕ)
    (f : Fin (n + 1) → (T ⟶ A)) (i : Fin (n + 1)) :
    nonemptySSetPowerLift n f ≫ nonemptySSetPowerProjection A n i = f i := by
  induction n with
  | zero =>
    have hi : i = 0 := Fin.eq_zero i
    subst i
    exact Category.comp_id _
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · exact CartesianMonoidalCategory.lift_fst _ _
    · change CartesianMonoidalCategory.lift _ _ ≫
        (CartesianMonoidalCategory.snd _ _ ≫ nonemptySSetPowerProjection A n j) = _
      rw [← Category.assoc, CartesianMonoidalCategory.lift_snd]
      exact ih _ j

/-- 正の有限積への標準の射は始域の射の前合成と厳密に可換。 -/
lemma nonemptySSetPowerLift_comp {T U A : SSet.{u}} (n : ℕ)
    (g : T ⟶ U) (f : Fin (n + 1) → (U ⟶ A)) :
    g ≫ nonemptySSetPowerLift n f = nonemptySSetPowerLift n (fun i => g ≫ f i) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change g ≫ CartesianMonoidalCategory.lift _ _ = CartesianMonoidalCategory.lift _ _
    rw [CartesianMonoidalCategory.comp_lift, ih]

end SerrePositivity.KST.SConstruction
