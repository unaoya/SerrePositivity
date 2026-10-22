module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraProInverseRoofFactor

/-!
概要：元の塔の pro 逆を、次数全射準同型を分母とする実 roof と両三角形で表す。
方針：各段の元の span を先に選び、その同じ span の像を全ての反転関手で比較する。
規約：実際に構成した場合だけ提供する性質。使われ方：class 逆の抽出と再利用。
-/

@[expose] public section
noncomputable section
universe u v w
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
open ProExcision
variable (R : Type u) [CommRing R] {D : Type v} [Category.{w} D]
  {X Y Z : Tower (Mon (Complex R))}

def HasSurjectiveRoofProInverse (f : LevelHom X Y) : Prop :=
  ∀ i, ∃ m, ∃ hi : i ≤ m, ∃ r : SurjectiveRoof R (Y.obj m) (X.obj i),
    ∀ (L : Mon (Complex R) ⥤ D) (hL : InvertsQuasiIsos R L),
      L.map (f.app m) ≫ r.value R L hL = L.map (X.transition hi) ∧
        r.value R L hL ≫ L.map (f.app i) = L.map (Y.transition hi)

def HasConnectiveRoofProInverse (f : LevelHom X Y)
    (hY : ∀ i, IsConnective R (Y.obj i)) : Prop :=
  ∀ i, ∃ m, ∃ hi : i ≤ m, ∃ r : SurjectiveRoof R (Y.obj m) (X.obj i),
    ∀ (L : Mon (Complex R) ⥤ D) (hL : InvertsConnectiveQuasiIsos R L),
      L.map (f.app m) ≫ r.connectiveValue R L hL (hY m) = L.map (X.transition hi) ∧
        r.connectiveValue R L hL (hY m) ≫ L.map (f.app i) = L.map (Y.transition hi)

lemma HasSurjectiveRoofProInverse.isProIso {f : LevelHom X Y}
    (h : HasSurjectiveRoofProInverse R (D := D) f)
    (L : Mon (Complex R) ⥤ D) (hL : InvertsQuasiIsos R L) : IsProIso (f.map L) := by
  intro i
  obtain ⟨m, hi, r, hr⟩ := h i
  exact ⟨m, hi, r.value R L hL, hr L hL⟩

lemma HasConnectiveRoofProInverse.isProIso {f : LevelHom X Y}
    {hY : ∀ i, IsConnective R (Y.obj i)} (h : HasConnectiveRoofProInverse R (D := D) f hY)
    (L : Mon (Complex R) ⥤ D) (hL : InvertsConnectiveQuasiIsos R L) : IsProIso (f.map L) := by
  intro i
  obtain ⟨m, hi, r, hr⟩ := h i
  exact ⟨m, hi, r.connectiveValue R L hL (hY m), hr L hL⟩

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
