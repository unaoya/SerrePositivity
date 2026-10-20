module
public import SerrePositivity.KST.SConstruction.SerreIntervalMaxDiagonal
public import SerrePositivity.KST.SConstruction.SerreIntervalComonoidMaps

/-! # 元の max connection の余モノイド射
概要：元の max connection を、Serre 余モノイドの tensor からの射へ束ねる。
方針：元の増大・対角保存と tensor 余モノイドの signed 交差式を使う。
規約：基礎の chain map は元の max。使われ方：鎖立方体の connection と座標作用。
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

/-- 元の max connection を持つ Serre 余モノイド射。 -/
def serreIntervalMaxComonHom :
    serreIntervalComonoid A ⊗ serreIntervalComonoid A ⟶ serreIntervalComonoid A :=
  Comon.Hom.mk' (serreIntervalMax A)
    (by
      rw [Comon.tensorObj_counit]
      dsimp only [serreIntervalComonoid, Comon.mk, serreIntervalComonObj]
      exact serreIntervalMax_augmentation A)
    (by
      rw [Comon.tensorObj_comul]
      dsimp only [serreIntervalComonoid, Comon.mk, serreIntervalComonObj]
      simp only [Category.assoc]
      exact serreIntervalMax_diagonal A)

/-- connection の余モノイド射の基礎の chain map は、元の max そのもの。 -/
lemma serreIntervalMaxComonHom_hom :
    (serreIntervalMaxComonHom A).hom = serreIntervalMax A := rfl

end SerrePositivity.KST.SConstruction
