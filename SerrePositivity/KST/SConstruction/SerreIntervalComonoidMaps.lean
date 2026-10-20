module
public import SerrePositivity.KST.SConstruction.SerreCubeComonoid

/-! # 鎖区間の元の端点と増大の余モノイド射
概要：元の二つの端点と増大写像を、Serre 余モノイドの射へ束ねる。
方針：証明済みの端点の対角・増大の保存を使い、基礎の chain map を回収する。
規約：元の射そのものを保持する。使われ方：cubical 座標面と退化の対角保存。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 元の零端点による Serre 余モノイドの射。 -/
def serreIntervalZeroComonHom : Comon.trivial (Complex A) ⟶ serreIntervalComonoid A :=
  Comon.Hom.mk' (serreIntervalZero A) (serreIntervalAugmentation_zero A)
    (serreIntervalDiagonal_zero A)

/-- 元の一端点による Serre 余モノイドの射。 -/
def serreIntervalOneComonHom : Comon.trivial (Complex A) ⟶ serreIntervalComonoid A :=
  Comon.Hom.mk' (serreIntervalOne A) (serreIntervalAugmentation_one A)
    (serreIntervalDiagonal_one A)

/-- 元の増大写像による Serre 余モノイドの射。 -/
def serreIntervalAugmentationComonHom : serreIntervalComonoid A ⟶ Comon.trivial (Complex A) :=
  default

/-- 零端点の余モノイド射は、元の同じ chain map。 -/
lemma serreIntervalZeroComonHom_hom :
    (serreIntervalZeroComonHom A).hom = serreIntervalZero A := rfl

/-- 一端点の余モノイド射は、元の同じ chain map。 -/
lemma serreIntervalOneComonHom_hom :
    (serreIntervalOneComonHom A).hom = serreIntervalOne A := rfl

/-- 増大の余モノイド射は、元の同じ chain map。 -/
lemma serreIntervalAugmentationComonHom_hom :
    (serreIntervalAugmentationComonHom A).hom = serreIntervalAugmentation A := rfl

end SerrePositivity.KST.SConstruction
