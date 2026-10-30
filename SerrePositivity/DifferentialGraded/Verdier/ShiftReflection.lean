module
public import SerrePositivity.CategoryTheory.Triangulated.VerdierLift

/-! # 忠実な前合成による比較自然変換の shift 整合性の反映 -/
@[expose] public section
noncomputable section
namespace SerrePositivity.DifferentialGraded
open CategoryTheory CategoryTheory.Functor
variable {M : Type*} [AddMonoid M] {B C D : Type*}
  [Category* B] [Category* C] [Category* D]
  [HasShift B M] [HasShift C M] [HasShift D M]
  (L : B ⥤ C) [L.CommShift M]
  [((whiskeringLeft B C D).obj L).Faithful]
  {F G : C ⥤ D} [F.CommShift M] [G.CommShift M] (τ : F ⟶ G)

/-- 前合成した比較が shift と可換なら、元の比較も同じ shift 構造と可換する。 -/
lemma natTransCommShift_of_precomp
    (hτ : NatTrans.CommShift (whiskerLeft L τ) M := by infer_instance) :
    NatTrans.CommShift τ M where
  shift_comm n := by
    let := hτ
    apply ((whiskeringLeft B C D).obj L).map_injective
    apply NatTrans.ext
    funext X
    apply (cancel_epi (F.map ((L.commShiftIso n).hom.app X))).1
    have h := NatTrans.shift_app_comm (whiskerLeft L τ) n X
    simp only [Functor.commShiftIso_comp_hom_app, whiskerLeft_app, Category.assoc] at h
    simpa only [Functor.whiskeringLeft_obj_map, whiskerLeft_app, NatTrans.comp_app,
      whiskerRight_app, Category.assoc, ← NatTrans.naturality_assoc] using h
end SerrePositivity.DifferentialGraded
