module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Ring.ULift

/-!
概要：p が零になる環への、小さい素体モデルの係数写像。
方針：ringChar の整除と ZMod の標準写像を宇宙の持ち上げへ合成する。
規約：CharP R p や非零環を仮定せず、零環も含める。
使われ方：有限型 F_p の模型の係数をそろえる（計画 E17）。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
universe u

/-- p が零になることから定まる、持ち上げた ZMod p の標準係数写像。 -/
def primeFieldRingHom (R : Type u) [CommRing R] (p : ℕ) (hR : (p : R) = 0) :
    ULift.{u} (ZMod p) →+* R :=
  (ZMod.castHom (ringChar.dvd hR) R).comp ULift.ringEquiv.toRingHom

end SerrePositivity.AlgebraicGeometry
