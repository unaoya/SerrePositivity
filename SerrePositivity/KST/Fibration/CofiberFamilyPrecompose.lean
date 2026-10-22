module
public import SerrePositivity.KST.Spectra.CofiberMappingFamilies

/-! # 元の基点固定 cofiber 写像族の、同じパラメータでの前合成 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.Fibration

/-- 元の点つき cofiber からの全写像族の降下は、パラメータの前合成を保つ。 -/
theorem cofiberFamilyDesc_precompose {B X P Q : SSet.{u}} (j : B ⟶ X)
    (Z : PointedSimplicialSet.{u}) (a : X ⊗ Q ⟶ Z.right)
    (ha : (j ▷ Q) ≫ a = toUnit _ ≫ Z.hom) (b : X ⊗ P ⟶ Z.right)
    (hb : (j ▷ P) ≫ b = toUnit _ ≫ Z.hom) (p : P ⟶ Q)
    (h : (𝟙 X ⊗ₘ p) ≫ a = b) :
    p ≫ cofiberFamilyDesc j Z a ha = cofiberFamilyDesc j Z b hb := by
  apply cofiberFamily_hom_ext j Z
  simp only [Category.assoc, cofiberFamilyDesc_restriction]
  apply uncurry_injective
  rw [uncurry_natural_left, uncurry_curry, uncurry_curry]
  simpa only [id_tensorHom] using h

end SerrePositivity.KST.Fibration
