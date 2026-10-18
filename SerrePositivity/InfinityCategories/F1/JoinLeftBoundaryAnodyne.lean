module

public import SerrePositivity.InfinityCategories.F1.JoinLeftBoundaryCorner
public import SerrePositivity.InfinityCategories.Core.RightFibration
public import SerrePositivity.InfinityCategories.Core.JoinLeftColimits

/-!
概要：right anodyne な左因子に対する join の相対境界の inner anodyne 性。
方針：単射の像を部分複体と見て、空の右部分複体との pushout-join に移す。
規約：任意の右因子を許し、モデル構造は使わない。
使われ方：Kerodon Proposition 4.3.6.4、Proposition 5.2.4.5 の右錐への比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories

/-- 概要：部分複体の join の相対境界は空の右部分複体との pushout-join を与える。
方針：空の右 join の単位同型で既存の pushout の正方形を移送する。
規約：新しい右下の対象は二つの像の和の部分複体。
使われ方：Kerodon Proposition 4.3.6.4、任意の単射の像への移送。 -/
lemma joinLeftBoundary_subcomplex_isPushout {B : SSet.{u}} (A : B.Subcomplex) (K : SSet.{u}) :
    IsPushout (joinInl (A : SSet.{u}) K) A.ι
      (joinUnionLeft A (⊥ : K.Subcomplex))
      ((joinEmptyIso B K).inv ≫ joinUnionRight A (⊥ : K.Subcomplex)) := by
  apply (joinUnion_isPushout A (⊥ : K.Subcomplex)).of_iso
    (joinEmptyIso (A : SSet.{u}) K) (Iso.refl _) (joinEmptyIso B K) (Iso.refl _)
  · apply (cancel_epi (joinEmptyIso (A : SSet.{u}) K).inv).1
    rw [← Category.assoc, joinEmptyIso_inv, joinInl_joinMap, Category.id_comp]
    simp only [← joinEmptyIso_inv, Iso.refl_hom, Category.comp_id, Iso.inv_hom_id_assoc]
  · exact joinEmptyIso_naturality A.ι K
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
  · simp only [Iso.refl_hom, Category.comp_id, ← Category.assoc,
      Iso.hom_inv_id, Category.id_comp]

/-- 概要：right anodyne な単射の join の相対境界は inner anodyne。
方針：像への同型で部分複体版の pushout-join に移し、その包含の inner anodyne 性を使う。
規約：i の単射性は明示的に仮定する。
使われ方：Kerodon Proposition 4.3.6.4、Proposition 5.2.4.5 の円柱の右錐への拡張。 -/
lemma joinLeftBoundaryMap_innerAnodyne_of_rightAnodyne {A B : SSet.{u}}
    (i : A ⟶ B) [Mono i] (K : SSet.{u}) (hi : rightAnodyneExtensions i) :
    innerAnodyneExtensions (joinLeftBoundaryMap i K) := by
  let R := Subfunctor.range i
  let e : A ≅ (R : SSet.{u}) := asIso (Subfunctor.toRange i)
  have he : e.hom ≫ R.ι = i := Subfunctor.toRange_ι i
  have hR : rightAnodyneExtensions R.ι := by
    rwa [← rightAnodyneExtensions.cancel_left_of_respectsIso e.hom, he]
  let hs := joinLeftBoundary_subcomplex_isPushout R K
  let eK : join (R : SSet.{u}) K ≅ join A K :=
    (joinLeftFunctor K).mapIso e.symm
  have hp : IsPushout (joinInl A K) i
      (joinMap e.hom (𝟙 K) ≫ joinUnionLeft R (⊥ : K.Subcomplex))
      ((joinEmptyIso B K).inv ≫ joinUnionRight R (⊥ : K.Subcomplex)) := by
    apply hs.of_iso e.symm eK (Iso.refl B) (Iso.refl _)
    · change joinInl (R : SSet.{u}) K ≫ joinMap e.inv (𝟙 K) = e.inv ≫ joinInl A K
      simpa only [Category.id_comp] using joinInl_joinMap e.inv (𝟙 K)
    · simp only [Iso.refl_hom, Category.comp_id, Iso.symm_hom]
      rw [← he, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
    · change joinUnionLeft R (⊥ : K.Subcomplex) ≫ 𝟙 _ =
        joinMap e.inv (𝟙 K) ≫ (joinMap e.hom (𝟙 K) ≫ _)
      simp only [Category.comp_id, ← Category.assoc, ← joinMap_comp,
        Iso.inv_hom_id, Category.id_comp, joinMap_id]
    · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
  have hm : joinLeftBoundaryMap i K = hp.isoPushout.inv ≫ (joinUnion R (⊥ : K.Subcomplex)).ι := by
    apply pushout.hom_ext
    · rw [joinLeftBoundaryMap_join, ← Category.assoc, hp.inl_isoPushout_inv,
        Category.assoc, joinUnionLeft_ι, ← joinMap_comp, he, Category.id_comp]
    · rw [joinLeftBoundaryMap_left, ← Category.assoc, hp.inr_isoPushout_inv,
        Category.assoc, joinUnionRight_ι, joinEmptyIso_inv,
        joinInl_joinMap, Category.id_comp]
  rw [hm, innerAnodyneExtensions.cancel_left_of_respectsIso]
  exact joinUnion_innerAnodyne_of_rightAnodyne R (⊥ : K.Subcomplex) hR

end SerrePositivity.InfinityCategories
