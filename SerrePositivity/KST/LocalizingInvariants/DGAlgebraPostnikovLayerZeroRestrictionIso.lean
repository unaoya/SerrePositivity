module

public import SerrePositivity.KST.LocalizingInvariants.DGBimodulePostnikovTransition
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovZeroLayerBimodule
public import SerrePositivity.KST.LocalizingInvariants.BimoduleRestriction

/-!
概要：元の底変更層双加群と、その零底制限を underlying 恒等の実同型で比較する。
方針：元の底射の零切断への降下式と、集中係数の底切断遷移の作用比較を使う。
規約：同じ層と元の底射を保持。使われ方：共通零底の係数逆を元の roof 底へ戻す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] (B P : Mon (Complex R))
  [B.X.IsStrictlyLE 0] [P.X.IsStrictlyLE 0] (n : ℤ) (hn : 0 ≤ n) (b : P ⟶ postnikov R B n)

attribute [local instance] layerOriginal_upperBound layerOriginal_lowerBound
local instance zeroRestriction_target_lowerBound : (postnikov R B 0).X.IsStrictlyGE 0 := by
  simpa only [neg_zero] using postnikov_lowerBound R B 0

lemma postnikovLayerBase_zero_left_transition :
    ((postnikovTransition R B n 0 hn).hom ▷ postnikovLayer R B n) ≫
      (postnikovLayerZeroBimodule R B n).actLeft = (postnikovLayerBaseBimodule R B n hn).actLeft :=
  postnikovBimodule_left_transition R B (postnikovLayerOriginalBimodule R B n)
    (-(n + 1)) n 0 hn le_rfl hn

lemma postnikovLayerBase_zero_right_transition :
    (postnikovLayer R B n ◁ (postnikovTransition R B n 0 hn).hom) ≫
      (postnikovLayerZeroBimodule R B n).actRight =
        (postnikovLayerBaseBimodule R B n hn).actRight :=
  postnikovBimodule_right_transition R B (postnikovLayerOriginalBimodule R B n)
    (-(n + 1)) n 0 hn le_rfl hn

def postnikovLayerBaseZeroRestrictionIso :
    bimoduleRestrict b (postnikovLayerBaseBimodule R B n hn) ≅
    bimoduleRestrict (postnikovQuotient R P 0)
      (bimoduleRestrict (postnikovDesc R 0 (b ≫ postnikovTransition R B n 0 hn))
        (postnikovLayerZeroBimodule R B n)) := by
  have he : (postnikovQuotient R P 0).hom ≫
      (postnikovDesc R 0 (b ≫ postnikovTransition R B n 0 hn)).hom =
      b.hom ≫ (postnikovTransition R B n 0 hn).hom :=
    congrArg Mon.Hom.hom (postnikovQuotient_desc R 0 _)
  refine Bimod.isoOfIso (Iso.refl (postnikovLayer R B n)) ?_ ?_
  · change ((b.hom ▷ postnikovLayer R B n) ≫
      (postnikovLayerBaseBimodule R B n hn).actLeft) ≫ 𝟙 _ =
      (P.X ◁ 𝟙 (postnikovLayer R B n)) ≫
        ((postnikovQuotient R P 0).hom ▷ postnikovLayer R B n) ≫
          ((postnikovDesc R 0 (b ≫ postnikovTransition R B n 0 hn)).hom ▷
            postnikovLayer R B n) ≫ (postnikovLayerZeroBimodule R B n).actLeft
    simp only [Category.comp_id, whiskerLeft_id, Category.id_comp]
    rw [← comp_whiskerRight_assoc, he, comp_whiskerRight_assoc,
      postnikovLayerBase_zero_left_transition]
  · change ((postnikovLayer R B n ◁ b.hom) ≫
      (postnikovLayerBaseBimodule R B n hn).actRight) ≫ 𝟙 _ =
      (𝟙 (postnikovLayer R B n) ▷ P.X) ≫
        (postnikovLayer R B n ◁ (postnikovQuotient R P 0).hom) ≫
          (postnikovLayer R B n ◁ (postnikovDesc R 0 (b ≫ postnikovTransition R B n 0 hn)).hom) ≫
            (postnikovLayerZeroBimodule R B n).actRight
    simp only [Category.comp_id, id_whiskerRight, Category.id_comp]
    rw [← whiskerLeft_comp_assoc, he, whiskerLeft_comp_assoc,
      postnikovLayerBase_zero_right_transition]

lemma postnikovLayerBaseZeroRestrictionIso_hom :
    (postnikovLayerBaseZeroRestrictionIso R B P n hn b).hom.hom =
      𝟙 (postnikovLayer R B n) := rfl

lemma postnikovLayerBaseZeroRestrictionIso_inv :
    (postnikovLayerBaseZeroRestrictionIso R B P n hn b).inv.hom =
      𝟙 (postnikovLayer R B n) := rfl

lemma postnikovLayerBaseZeroRestriction_left :
    (bimoduleRestrict b (postnikovLayerBaseBimodule R B n hn)).actLeft =
      (bimoduleRestrict (postnikovQuotient R P 0)
        (bimoduleRestrict (postnikovDesc R 0 (b ≫ postnikovTransition R B n 0 hn))
          (postnikovLayerZeroBimodule R B n))).actLeft := by
  have h := (postnikovLayerBaseZeroRestrictionIso R B P n hn b).hom.left_act_hom
  rw [postnikovLayerBaseZeroRestrictionIso_hom] at h
  change (bimoduleRestrict b (postnikovLayerBaseBimodule R B n hn)).actLeft ≫
      𝟙 (bimoduleRestrict b (postnikovLayerBaseBimodule R B n hn)).X =
    (P.X ◁ 𝟙 (bimoduleRestrict b (postnikovLayerBaseBimodule R B n hn)).X) ≫ _ at h
  simpa only [Category.comp_id, whiskerLeft_id, Category.id_comp] using h

lemma postnikovLayerBaseZeroRestriction_right :
    (bimoduleRestrict b (postnikovLayerBaseBimodule R B n hn)).actRight =
      (bimoduleRestrict (postnikovQuotient R P 0)
        (bimoduleRestrict (postnikovDesc R 0 (b ≫ postnikovTransition R B n 0 hn))
          (postnikovLayerZeroBimodule R B n))).actRight := by
  have h := (postnikovLayerBaseZeroRestrictionIso R B P n hn b).hom.right_act_hom
  rw [postnikovLayerBaseZeroRestrictionIso_hom] at h
  change (bimoduleRestrict b (postnikovLayerBaseBimodule R B n hn)).actRight ≫
      𝟙 (bimoduleRestrict b (postnikovLayerBaseBimodule R B n hn)).X =
    (𝟙 (bimoduleRestrict b (postnikovLayerBaseBimodule R B n hn)).X ▷ P.X) ≫ _ at h
  simpa only [Category.comp_id, id_whiskerRight, Category.id_comp] using h

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
