module
public import SerrePositivity.KST.SConstruction.SerreIntervalMaxMonoid

/-! # 元の一端点の max 吸収と増大
概要：元の一端点は max の左右で吸収的で、max の増大は二因子の元の増大を回収する。
方針：元の chain map の吸収式を余モノイド射の外延性で移し、単位への射の一意性を使う。
規約：零端点の単位と一端点の吸収を区別する。使われ方：cubical connection と一端点の面。
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

/-- 元の一端点は max の左で吸収的な余モノイド射。 -/
lemma serreIntervalMaxComonHom_left_absorption :
    serreIntervalOneComonHom A ▷ serreIntervalComonoid A ≫ serreIntervalMaxComonHom A =
      (λ_ (serreIntervalComonoid A)).hom ≫ serreIntervalAugmentationComonHom A ≫
        serreIntervalOneComonHom A := by
  apply Comon.Hom.ext
  simp only [Comon.comp_hom', Comon.monoidal_whiskerRight_hom,
    serreIntervalOneComonHom_hom, serreIntervalAugmentationComonHom_hom,
    serreIntervalMaxComonHom_hom, comonoidLeftUnitorHom]
  dsimp only [serreIntervalComonoid, Comon.mk, Comon.trivial]
  exact serreIntervalMax_one_left A

/-- 元の一端点は max の右でも吸収的な余モノイド射。 -/
lemma serreIntervalMaxComonHom_right_absorption :
    serreIntervalComonoid A ◁ serreIntervalOneComonHom A ≫ serreIntervalMaxComonHom A =
      (ρ_ (serreIntervalComonoid A)).hom ≫ serreIntervalAugmentationComonHom A ≫
        serreIntervalOneComonHom A := by
  apply Comon.Hom.ext
  simp only [Comon.comp_hom', Comon.monoidal_whiskerLeft_hom,
    serreIntervalOneComonHom_hom, serreIntervalAugmentationComonHom_hom,
    serreIntervalMaxComonHom_hom, comonoidRightUnitorHom]
  dsimp only [serreIntervalComonoid, Comon.mk, Comon.trivial]
  apply (cancel_epi (ρ_ (serreInterval A)).inv).1
  rw [Iso.inv_hom_id_assoc]
  exact serreIntervalMax_one_right A

/-- 元の max の増大は、二つの元の増大と同じ単位射を回収する。 -/
lemma serreIntervalMaxComonHom_augmentation :
    serreIntervalMaxComonHom A ≫ serreIntervalAugmentationComonHom A =
      (serreIntervalAugmentationComonHom A ⊗ₘ serreIntervalAugmentationComonHom A) ≫
        (λ_ (𝟙_ (Comon (Complex A)))).hom :=
  Subsingleton.elim _ _

end SerrePositivity.KST.SConstruction
