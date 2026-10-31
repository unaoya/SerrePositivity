module

public import SerrePositivity.KST.Spectra.PointedUncurryActionTensor
public import SerrePositivity.KST.Spectra.SuspensionComposition

/-!
概要：元の uncurry 作用は、源の懸垂作用と全 Hom の豊穣合成に対して厳密に整合する。
方針：閉構造の合成の標的自然性と懸垂の合成保存を、同じ評価へ適用する。
規約：頂点ごとの一致を使わない。使われ方：全族入力に沿う uncurry 座標の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory MonoidalCategory MonoidalClosed
namespace SerrePositivity.KST.Spectra.PointedMapping

private lemma closedComp_post {D : Type u} [Category.{v} D] [MonoidalCategory D]
    [MonoidalClosed D] (A B : D) {V W : D} (b : V ⟶ W) :
    MonoidalClosed.comp A B V ≫ (ihom A).map b =
      ((𝟙 ((ihom A).obj B)) ⊗ₘ (ihom B).map b) ≫ MonoidalClosed.comp A B W := by
  apply uncurry_injective
  rw [uncurry_natural_right, uncurry_natural_left]
  simp only [comp_eq, uncurry_curry, compTranspose_eq, tensorHom_def,
    id_whiskerRight, Category.id_comp]
  rw [associator_inv_naturality_right_assoc, whisker_exchange_assoc,
    (ihom.ev B).naturality b]

/-- 豊穣合成を uncurry することは、第一入力の懸垂と第二入力の uncurry を合成すること。 -/
lemma uncurryAction_comp (A B W : PointedSimplicialSet.{u}) :
    MonoidalClosed.comp A B (loopSpace W) ≫ uncurryAction A W =
      (suspensionHom A B ⊗ₘ uncurryAction B W) ≫
        MonoidalClosed.comp (suspension A) (suspension B) W := by
  have hc := closedComp_post (suspension A) (suspension B)
    ((ihom.ev PointedSimplicialSet.circle.{u}).app W)
  change MonoidalClosed.comp (suspension A) (suspension B) (suspension (loopSpace W)) ≫
      PointedObject.basedHomMap (suspension A)
        ((ihom.ev PointedSimplicialSet.circle.{u}).app W) =
    (𝟙 (PointedObject.basedHom (suspension A) (suspension B)) ⊗ₘ
      PointedObject.basedHomMap (suspension B)
        ((ihom.ev PointedSimplicialSet.circle.{u}).app W)) ≫
      MonoidalClosed.comp (suspension A) (suspension B) W at hc
  dsimp only [uncurryAction]
  rw [← Category.assoc, suspensionHom_comp, Category.assoc, hc]
  rw [← Category.assoc, ← tensorHom_comp]
  simp only [Category.comp_id]

end SerrePositivity.KST.Spectra.PointedMapping
