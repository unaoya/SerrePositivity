module
public import SerrePositivity.KST.SConstruction.SerreCubeTensorIso

/-! # 四つの次元を固定した元の鎖 tensor 射
概要：左右の鎖立方体の射の tensor を、全ての対象を明示して与える。
方針：元の tensor 射を、その四つの鎖立方体を固定したまま使う。
規約：元の因子順と signed tensor を保持する。使われ方：連結比較の自然性。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 四つの次元を明示した、元の鎖立方体の tensor 射。 -/
def serreCubeTensorHom {n p m q : ℕ}
    (f : serreCubeComonoid A n ⟶ serreCubeComonoid A p)
    (g : serreCubeComonoid A m ⟶ serreCubeComonoid A q) :
    serreCubeComonoid A n ⊗ serreCubeComonoid A m ⟶
      serreCubeComonoid A p ⊗ serreCubeComonoid A q :=
  @tensorHom (Comon (Complex A)) _ _ (serreCubeComonoid A n) (serreCubeComonoid A p)
    (serreCubeComonoid A m) (serreCubeComonoid A q) f g

end SerrePositivity.KST.SConstruction
