module

public import SerrePositivity.InfinityCategories.Core.FatJoinFunctor
public import Mathlib.CategoryTheory.Monoidal.Closed.Types

/-!
概要：fat join の左因子の pushout の保存。
方針：円柱と左因子の pushout から射を作り、固定した右因子と貼る。
規約：単射性を要求しない通常の pushout を扱う。
使われ方：Kerodon Lemma 4.6.2.10 のセル分解による比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：左因子の pushout は固定した右因子との fat join 後も pushout。
方針：円柱の直積が pushout を保つことと fat join の三つの制限の普遍性を使う。
規約：貼り合わせる射に単射性は不要。
使われ方：Kerodon Lemma 4.6.2.10 の貼り合わせ。 -/
lemma fatJoin_left_isPushout {A B C D : SSet.{u}}
    {f : A ⟶ B} {g : A ⟶ C} {r : B ⟶ D} {t : C ⟶ D}
    (h : IsPushout f g r t) (K : SSet.{u}) :
    IsPushout (fatJoinMap f (𝟙 K)) (fatJoinMap g (𝟙 K))
      (fatJoinMap r (𝟙 K)) (fatJoinMap t (𝟙 K)) := by
  have hw : fatJoinMap f (𝟙 K) ≫ fatJoinMap r (𝟙 K) =
      fatJoinMap g (𝟙 K) ≫ fatJoinMap t (𝟙 K) := by
    rw [fatJoinMap_comp, fatJoinMap_comp, h.w]
  have hC : IsPushout (fatJoinCylinderMap f (𝟙 K)) (fatJoinCylinderMap g (𝟙 K))
      (fatJoinCylinderMap r (𝟙 K)) (fatJoinCylinderMap t (𝟙 K)) :=
    h.map (tensorRight (Δ[1] : SSet.{u}) ⋙ tensorRight K)
  have hT := h.map (tensorRight K)
  apply IsPushout.mk' hw
  · intro X φ ψ h₁ h₂
    apply fatJoin_hom_ext
    · apply hC.hom_ext
      · simpa only [reassoc_of% fatJoinCylinder_map] using
          congrArg (fun z : fatJoin B K ⟶ X ↦ fatJoinCylinder B K ≫ z) h₁
      · simpa only [reassoc_of% fatJoinCylinder_map] using
          congrArg (fun z : fatJoin C K ⟶ X ↦ fatJoinCylinder C K ≫ z) h₂
    · apply h.hom_ext
      · simpa only [reassoc_of% fatJoinInl_map] using
          congrArg (fun z : fatJoin B K ⟶ X ↦ fatJoinInl B K ≫ z) h₁
      · simpa only [reassoc_of% fatJoinInl_map] using
          congrArg (fun z : fatJoin C K ⟶ X ↦ fatJoinInl C K ≫ z) h₂
    · simpa only [reassoc_of% fatJoinInr_map, Category.id_comp] using
        congrArg (fun z : fatJoin B K ⟶ X ↦ fatJoinInr B K ≫ z) h₁
  · intro X b c hbc
    have hl : f ≫ (fatJoinInl B K ≫ b) = g ≫ (fatJoinInl C K ≫ c) := by
      simpa only [reassoc_of% fatJoinInl_map] using
        congrArg (fun z : fatJoin A K ⟶ X ↦ fatJoinInl A K ≫ z) hbc
    have hr : fatJoinInr C K ≫ c = fatJoinInr B K ≫ b := by
      simpa only [reassoc_of% fatJoinInr_map, Category.id_comp] using
        (congrArg (fun z : fatJoin A K ⟶ X ↦ fatJoinInr A K ≫ z) hbc).symm
    have hH : fatJoinCylinderMap f (𝟙 K) ≫ (fatJoinCylinder B K ≫ b) =
        fatJoinCylinderMap g (𝟙 K) ≫ (fatJoinCylinder C K ≫ c) := by
      simpa only [reassoc_of% fatJoinCylinder_map] using
        congrArg (fun z : fatJoin A K ⟶ X ↦ fatJoinCylinder A K ≫ z) hbc
    let l := h.desc (fatJoinInl B K ≫ b) (fatJoinInl C K ≫ c) hl
    let k := fatJoinInr B K ≫ b
    let H := hC.desc (fatJoinCylinder B K ≫ b) (fatJoinCylinder C K ≫ c) hH
    have hlB : r ≫ l = fatJoinInl B K ≫ b := h.inl_desc _ _ _
    have hlC : t ≫ l = fatJoinInl C K ≫ c := h.inr_desc _ _ _
    have hHB : fatJoinCylinderMap r (𝟙 K) ≫ H = fatJoinCylinder B K ≫ b :=
      hC.inl_desc _ _ _
    have hHC : fatJoinCylinderMap t (𝟙 K) ≫ H = fatJoinCylinder C K ≫ c :=
      hC.inr_desc _ _ _
    have h₀ : (SSet.ι₀ (X := D) ▷ K) ≫ H = fst D K ≫ l := by
      apply hT.hom_ext
      · change (r ⊗ₘ 𝟙 K) ≫ _ = (r ⊗ₘ 𝟙 K) ≫ _
        rw [← Category.assoc, ← fatJoinCylinderMap_zero, Category.assoc, hHB,
          ← Category.assoc, fatJoinCylinder_zero, Category.assoc,
          reassoc_of% tensorHom_fst, hlB]
      · change (t ⊗ₘ 𝟙 K) ≫ _ = (t ⊗ₘ 𝟙 K) ≫ _
        rw [← Category.assoc, ← fatJoinCylinderMap_zero, Category.assoc, hHC,
          ← Category.assoc, fatJoinCylinder_zero, Category.assoc,
          reassoc_of% tensorHom_fst, hlC]
    have h₁ : (SSet.ι₁ (X := D) ▷ K) ≫ H = snd D K ≫ k := by
      apply hT.hom_ext
      · change (r ⊗ₘ 𝟙 K) ≫ _ = (r ⊗ₘ 𝟙 K) ≫ _
        rw [← Category.assoc, ← fatJoinCylinderMap_one, Category.assoc, hHB,
          ← Category.assoc, fatJoinCylinder_one, Category.assoc,
          reassoc_of% tensorHom_snd, Category.id_comp]
      · change (t ⊗ₘ 𝟙 K) ≫ _ = (t ⊗ₘ 𝟙 K) ≫ _
        rw [← Category.assoc, ← fatJoinCylinderMap_one, Category.assoc, hHC,
          ← Category.assoc, fatJoinCylinder_one, Category.assoc,
          reassoc_of% tensorHom_snd, Category.id_comp, hr]
    let F := fatJoinDesc l k H h₀ h₁
    have hFc : fatJoinCylinder D K ≫ F = H := fatJoinCylinder_desc _ _ _ _ _
    have hFl : fatJoinInl D K ≫ F = l := fatJoinInl_desc _ _ _ _ _
    have hFr : fatJoinInr D K ≫ F = k := fatJoinInr_desc _ _ _ _ _
    refine ⟨F, ?_, ?_⟩
    · apply fatJoin_hom_ext
      · rw [← Category.assoc, fatJoinCylinder_map, Category.assoc, hFc, hHB]
      · rw [← Category.assoc, fatJoinInl_map, Category.assoc, hFl, hlB]
      · rw [← Category.assoc, fatJoinInr_map, Category.id_comp, hFr]
    · apply fatJoin_hom_ext
      · rw [← Category.assoc, fatJoinCylinder_map, Category.assoc, hFc, hHC]
      · rw [← Category.assoc, fatJoinInl_map, Category.assoc, hFl, hlC]
      · rw [← Category.assoc, fatJoinInr_map, Category.id_comp, hFr]
        exact hr.symm

/-- 概要：右因子の pushout は固定した左因子との fat join 後も pushout。
方針：円柱の直積が pushout を保つことと fat join の三つの制限の普遍性を使う。
規約：貼り合わせる射に単射性は不要。
使われ方：Kerodon Lemma 4.6.2.10 の貼り合わせ。 -/
lemma fatJoin_right_isPushout {A B C D : SSet.{u}}
    {f : A ⟶ B} {g : A ⟶ C} {r : B ⟶ D} {t : C ⟶ D}
    (h : IsPushout f g r t) (K : SSet.{u}) :
    IsPushout (fatJoinMap (𝟙 K) f) (fatJoinMap (𝟙 K) g)
      (fatJoinMap (𝟙 K) r) (fatJoinMap (𝟙 K) t) := by
  have hw : fatJoinMap (𝟙 K) f ≫ fatJoinMap (𝟙 K) r =
      fatJoinMap (𝟙 K) g ≫ fatJoinMap (𝟙 K) t := by
    rw [fatJoinMap_comp, fatJoinMap_comp, h.w]
  have hC : IsPushout (fatJoinCylinderMap (𝟙 K) f) (fatJoinCylinderMap (𝟙 K) g)
      (fatJoinCylinderMap (𝟙 K) r) (fatJoinCylinderMap (𝟙 K) t) :=
    h.map (tensorLeft (K ⊗ (Δ[1] : SSet.{u})))
  have hT := h.map (tensorLeft K)
  apply IsPushout.mk' hw
  · intro X φ ψ h₁ h₂
    apply fatJoin_hom_ext
    · apply hC.hom_ext
      · simpa only [reassoc_of% fatJoinCylinder_map] using
          congrArg (fun z : fatJoin K B ⟶ X ↦ fatJoinCylinder K B ≫ z) h₁
      · simpa only [reassoc_of% fatJoinCylinder_map] using
          congrArg (fun z : fatJoin K C ⟶ X ↦ fatJoinCylinder K C ≫ z) h₂
    · simpa only [reassoc_of% fatJoinInl_map, Category.id_comp] using
        congrArg (fun z : fatJoin K B ⟶ X ↦ fatJoinInl K B ≫ z) h₁
    · apply h.hom_ext
      · simpa only [reassoc_of% fatJoinInr_map] using
          congrArg (fun z : fatJoin K B ⟶ X ↦ fatJoinInr K B ≫ z) h₁
      · simpa only [reassoc_of% fatJoinInr_map] using
          congrArg (fun z : fatJoin K C ⟶ X ↦ fatJoinInr K C ≫ z) h₂
  · intro X b c hbc
    have hl : f ≫ (fatJoinInr K B ≫ b) = g ≫ (fatJoinInr K C ≫ c) := by
      simpa only [reassoc_of% fatJoinInr_map] using
        congrArg (fun z : fatJoin K A ⟶ X ↦ fatJoinInr K A ≫ z) hbc
    have hr : fatJoinInl K C ≫ c = fatJoinInl K B ≫ b := by
      simpa only [reassoc_of% fatJoinInl_map, Category.id_comp] using
        (congrArg (fun z : fatJoin K A ⟶ X ↦ fatJoinInl K A ≫ z) hbc).symm
    have hH : fatJoinCylinderMap (𝟙 K) f ≫ (fatJoinCylinder K B ≫ b) =
        fatJoinCylinderMap (𝟙 K) g ≫ (fatJoinCylinder K C ≫ c) := by
      simpa only [reassoc_of% fatJoinCylinder_map] using
        congrArg (fun z : fatJoin K A ⟶ X ↦ fatJoinCylinder K A ≫ z) hbc
    let l := h.desc (fatJoinInr K B ≫ b) (fatJoinInr K C ≫ c) hl
    let k := fatJoinInl K B ≫ b
    let H := hC.desc (fatJoinCylinder K B ≫ b) (fatJoinCylinder K C ≫ c) hH
    have hlB : r ≫ l = fatJoinInr K B ≫ b := h.inl_desc _ _ _
    have hlC : t ≫ l = fatJoinInr K C ≫ c := h.inr_desc _ _ _
    have hHB : fatJoinCylinderMap (𝟙 K) r ≫ H = fatJoinCylinder K B ≫ b :=
      hC.inl_desc _ _ _
    have hHC : fatJoinCylinderMap (𝟙 K) t ≫ H = fatJoinCylinder K C ≫ c :=
      hC.inr_desc _ _ _
    have h₀ : (SSet.ι₀ (X := K) ▷ D) ≫ H = fst K D ≫ k := by
      apply hT.hom_ext
      · change (𝟙 K ⊗ₘ r) ≫ _ = (𝟙 K ⊗ₘ r) ≫ _
        rw [← Category.assoc, ← fatJoinCylinderMap_zero, Category.assoc, hHB,
          ← Category.assoc, fatJoinCylinder_zero, Category.assoc,
          reassoc_of% tensorHom_fst, Category.id_comp]
      · change (𝟙 K ⊗ₘ t) ≫ _ = (𝟙 K ⊗ₘ t) ≫ _
        rw [← Category.assoc, ← fatJoinCylinderMap_zero, Category.assoc, hHC,
          ← Category.assoc, fatJoinCylinder_zero, Category.assoc,
          reassoc_of% tensorHom_fst, Category.id_comp, hr]
    have h₁ : (SSet.ι₁ (X := K) ▷ D) ≫ H = snd K D ≫ l := by
      apply hT.hom_ext
      · change (𝟙 K ⊗ₘ r) ≫ _ = (𝟙 K ⊗ₘ r) ≫ _
        rw [← Category.assoc, ← fatJoinCylinderMap_one, Category.assoc, hHB,
          ← Category.assoc, fatJoinCylinder_one, Category.assoc,
          reassoc_of% tensorHom_snd, hlB]
      · change (𝟙 K ⊗ₘ t) ≫ _ = (𝟙 K ⊗ₘ t) ≫ _
        rw [← Category.assoc, ← fatJoinCylinderMap_one, Category.assoc, hHC,
          ← Category.assoc, fatJoinCylinder_one, Category.assoc,
          reassoc_of% tensorHom_snd, hlC]
    let F := fatJoinDesc k l H h₀ h₁
    have hFc : fatJoinCylinder K D ≫ F = H := fatJoinCylinder_desc _ _ _ _ _
    have hFl : fatJoinInr K D ≫ F = l := fatJoinInr_desc _ _ _ _ _
    have hFr : fatJoinInl K D ≫ F = k := fatJoinInl_desc _ _ _ _ _
    refine ⟨F, ?_, ?_⟩
    · apply fatJoin_hom_ext
      · rw [← Category.assoc, fatJoinCylinder_map, Category.assoc, hFc, hHB]
      · rw [← Category.assoc, fatJoinInl_map, Category.id_comp, hFr]
      · rw [← Category.assoc, fatJoinInr_map, Category.assoc, hFl, hlB]
    · apply fatJoin_hom_ext
      · rw [← Category.assoc, fatJoinCylinder_map, Category.assoc, hFc, hHC]
      · rw [← Category.assoc, fatJoinInl_map, Category.id_comp, hFr]
        exact hr.symm
      · rw [← Category.assoc, fatJoinInr_map, Category.assoc, hFl, hlC]

end SerrePositivity.InfinityCategories
