module
public import SerrePositivity.DifferentialGraded.Derived.Triangulated
public import Mathlib.CategoryTheory.Localization.Linear

/-! # 指定導来局所化の加法性と標準A線形構造への接続 -/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 既存のK(D)経由の因子化から主局所化の加法性を得る。
これによりMathlibの局所化の標準Linear構造と関手の線形性が適用できる。 -/
instance moduleToDerivedAdditive : (moduleToDerived A D).Additive :=
  Functor.additive_of_iso (moduleToHomotopyDerivedIso A D)

end SerrePositivity.DifferentialGraded
