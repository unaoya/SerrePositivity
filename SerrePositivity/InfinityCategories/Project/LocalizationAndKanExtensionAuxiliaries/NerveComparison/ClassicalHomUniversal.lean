module

public import Mathlib.CategoryTheory.Functor.KanExtension.Basic

/-!
概要：通常の左右 Kan 拡張を自然変換の全単射で判定する。
方針：構造化射の始対象・終対象の普遍性を使う。
規約：点ごとの Kan 条件とは別の大域的な普遍性。
使われ方：B5 の通常の Kan 拡張との比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits
namespace SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison

/-- 概要：通常の左 Kan 拡張は指定単位による自然変換の全単射と同値。
方針：全単射の逆で構造化射の始対象を構成する。
規約：全ての比較関手についての普遍性。
使われ方：大域的な Kan 普遍性の古典比較。 -/
lemma kanClassical_isLeftKanExtension_iff_bijective {K C D : Type u}
    [Category.{u} K] [Category.{u} C] [Category.{u} D]
    (L : K ⥤ C) (F₀ : K ⥤ D) (F : C ⥤ D) (β : F₀ ⟶ L ⋙ F) :
    F.IsLeftKanExtension β ↔ ∀ G : C ⥤ D,
      Function.Bijective (fun η : F ⟶ G ↦ β ≫ Functor.whiskerLeft L η) := by
  constructor
  · intro h G
    let := h
    exact (F.homEquivOfIsLeftKanExtension β G).bijective
  · intro h
    let e (G : C ⥤ D) := Equiv.ofBijective _ (h G)
    refine ⟨⟨IsInitial.ofUniqueHom (fun E ↦ StructuredArrow.homMk
      ((e E.right).symm E.hom) ((e E.right).apply_symm_apply E.hom)) ?_⟩⟩
    intro E m
    apply StructuredArrow.hom_ext
    apply (e E.right).injective
    exact m.w.trans ((e E.right).apply_symm_apply E.hom).symm

/-- 概要：通常の右 Kan 拡張は指定余単位による自然変換の全単射と同値。
方針：全単射の逆を使い余構造化射の終対象を構成する。
規約：点ごとの極限性は仮定しない。
使われ方：右 Kan の大域的比較。 -/
lemma kanClassical_isRightKanExtension_iff_bijective {K C D : Type u}
    [Category.{u} K] [Category.{u} C] [Category.{u} D]
    (L : K ⥤ C) (F₀ : K ⥤ D) (F : C ⥤ D) (α : L ⋙ F ⟶ F₀) :
    F.IsRightKanExtension α ↔ ∀ G : C ⥤ D,
      Function.Bijective (fun η : G ⟶ F ↦ Functor.whiskerLeft L η ≫ α) := by
  constructor
  · intro h G
    let := h
    exact (F.homEquivOfIsRightKanExtension α G).bijective
  · intro h
    let e (G : C ⥤ D) := Equiv.ofBijective _ (h G)
    refine ⟨⟨IsTerminal.ofUniqueHom (fun E ↦ CostructuredArrow.homMk
      ((e E.left).symm E.hom) ((e E.left).apply_symm_apply E.hom)) ?_⟩⟩
    intro E m
    apply CostructuredArrow.hom_ext
    apply (e E.left).injective
    exact m.w.trans ((e E.left).apply_symm_apply E.hom).symm

end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison
