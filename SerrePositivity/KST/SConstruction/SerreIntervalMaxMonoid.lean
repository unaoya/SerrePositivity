module
public import SerrePositivity.KST.SConstruction.SerreIntervalMaxAssociativity
public import SerrePositivity.KST.SConstruction.SerreIntervalMaxComonoid
public import SerrePositivity.KST.SConstruction.ComonoidStructureMaps

/-! # Serre 余モノイド上の元の max モノイド
概要：元の零端点を単位、max connection を積とする余モノイド圏のモノイドを作る。
方針：基礎の chain map の単位・結合則を、余モノイド射の外延性で回収する。
規約：Serre 対角と元の max を保つ。使われ方：cubical connection の全座標の関係式。
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

/-- 余モノイド射としての max の左単位は、元の零端点。 -/
lemma serreIntervalMaxComonHom_left_unit :
    serreIntervalZeroComonHom A ▷ serreIntervalComonoid A ≫ serreIntervalMaxComonHom A =
      (λ_ (serreIntervalComonoid A)).hom := by
  apply Comon.Hom.ext
  simp only [Comon.comp_hom', Comon.monoidal_whiskerRight_hom,
    serreIntervalZeroComonHom_hom, serreIntervalMaxComonHom_hom, comonoidLeftUnitorHom]
  dsimp only [serreIntervalComonoid, Comon.mk, Comon.trivial]
  exact serreIntervalMax_zero_left A

/-- 余モノイド射としての max の右単位は、元の零端点。 -/
lemma serreIntervalMaxComonHom_right_unit :
    serreIntervalComonoid A ◁ serreIntervalZeroComonHom A ≫ serreIntervalMaxComonHom A =
      (ρ_ (serreIntervalComonoid A)).hom := by
  apply Comon.Hom.ext
  simp only [Comon.comp_hom', Comon.monoidal_whiskerLeft_hom,
    serreIntervalZeroComonHom_hom, serreIntervalMaxComonHom_hom, comonoidRightUnitorHom]
  dsimp only [serreIntervalComonoid, Comon.mk, Comon.trivial]
  apply (cancel_epi (ρ_ (serreInterval A)).inv).1
  rw [Iso.inv_hom_id]
  exact serreIntervalMax_zero_right A

/-- 元の max の結合則は、同じ Serre 余モノイド圏で成立する。 -/
lemma serreIntervalMaxComonHom_assoc :
    serreIntervalMaxComonHom A ▷ serreIntervalComonoid A ≫ serreIntervalMaxComonHom A =
      (α_ (serreIntervalComonoid A) (serreIntervalComonoid A) (serreIntervalComonoid A)).hom ≫
        (serreIntervalComonoid A ◁ serreIntervalMaxComonHom A) ≫ serreIntervalMaxComonHom A := by
  apply Comon.Hom.ext
  simp only [Comon.comp_hom', Comon.monoidal_whiskerRight_hom,
    Comon.monoidal_whiskerLeft_hom, serreIntervalMaxComonHom_hom, comonoidAssociatorHom]
  dsimp only [serreIntervalComonoid, Comon.mk, Comon.trivial]
  simpa only [tensorHom_id, id_tensorHom] using serreIntervalMax_assoc A

/-- 元の零端点・max を単位・積とする、Serre 余モノイドのモノイド構造。 -/
instance serreIntervalMaxMonObj : MonObj (serreIntervalComonoid A) where
  one := serreIntervalZeroComonHom A
  mul := serreIntervalMaxComonHom A
  one_mul := serreIntervalMaxComonHom_left_unit A
  mul_one := serreIntervalMaxComonHom_right_unit A
  mul_assoc := serreIntervalMaxComonHom_assoc A

/-- 元の Serre 余モノイドを持つ max モノイド。 -/
def serreIntervalMaxMonoid : Mon (Comon (Complex A)) := Mon.mk (serreIntervalComonoid A)

end SerrePositivity.KST.SConstruction
