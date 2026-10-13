module

public import SerrePositivity.CommutativeAlgebra.Almost.Category
public import SerrePositivity.CommutativeAlgebra.PowTorsionCategory

/-! # 冪ねじれ加群の almost 局所化

J の一つの冪で消える加群の圏を、I で消える加群の Serre 類で割る。
長さの加法性の定義域を保つため、全加群の almost 圏とは別に構成する。
CLMST の長さ比較では、この圏での同型を使う。
-/

@[expose] public section
universe u
namespace SerrePositivity.Almost
open CategoryTheory CategoryTheory.Limits

variable {R : Type u} [CommRing R] (I J : Ideal R) [Fact (I * I = I)]

/-- 冪ねじれ加群の中で I により消える対象の性質。 -/
def torsionZeroObjects : ObjectProperty (PowTorsionModule J) :=
  (zeroObjects I).inverseImage (powTorsionModule J).ι

instance : (torsionZeroObjects I J).IsSerreClass := inferInstanceAs
  ((zeroObjects I).inverseImage (powTorsionModule J).ι).IsSerreClass

/-- J 冪ねじれ加群の almost 圏。I 零の核・余核を持つ射を反転する。 -/
abbrev TorsionModuleCategory := (torsionZeroObjects I J).isoModSerre.Localization

/-- 冪ねじれ加群の almost 局所化関手。 -/
noncomputable abbrev torsionLocalization :
    PowTorsionModule J ⥤ TorsionModuleCategory I J :=
  (torsionZeroObjects I J).isoModSerre.Q

noncomputable instance : PreservesFiniteLimits (torsionLocalization I J) :=
  ObjectProperty.SerreClassLocalization.preservesFiniteLimits
    (torsionLocalization I J) (torsionZeroObjects I J)

noncomputable instance : PreservesFiniteColimits (torsionLocalization I J) :=
  ObjectProperty.SerreClassLocalization.preservesFiniteColimits
    (torsionLocalization I J) (torsionZeroObjects I J)

/-- 冪ねじれ対象が almost 圏で零になることと、I で消えることは同値。 -/
theorem isZero_torsionLocalization_obj_iff (M : PowTorsionModule J) :
    IsZero ((torsionLocalization I J).obj M) ↔ IsAlmostZero I M.obj :=
  ObjectProperty.SerreClassLocalization.isZero_obj_iff
    (torsionLocalization I J) (torsionZeroObjects I J) M

/-- 冪ねじれ対象の almost 同型は局所化圏での同型を意味する。 -/
def IsTorsionIsomorphic (M N : PowTorsionModule J) : Prop :=
  Nonempty ((torsionLocalization I J).obj M ≅ (torsionLocalization I J).obj N)

end SerrePositivity.Almost
