module
public import SerrePositivity.KST.NonConnective.SequentialLevelColimitMap

/-!
概要：元の段ごとの逐次 BF 余極限比較の恒等・合成を、同じ実注入で認証する。
方針：同じ通常余極限の一意性と元の比較射の脚の回収式を使う。
規約：対象・比較射・注入を変更しない。
使われ方：K-7 の実非連結化候補の比較を hSp へ渡す際の関手則。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits
namespace SerrePositivity.KST.NonConnective

/-- 概要：恒等自然変換の元の逐次段別余極限比較は実恒等射。
方針：同じ余極限の全注入後で比較する。
規約：元の選択余極限を保持する。
使われ方：非連結化候補の hSp 比較の恒等則。 -/
theorem sequentialLevelColimitMap_id (D : SpectrumSequence.{u}) :
    sequentialLevelColimitMap (𝟙 D) = 𝟙 (sequentialLevelColimitSpectrum D) := by
  apply (sequentialLevelColimitIsColimit D).hom_ext
  intro a
  change sequentialLevelColimitInjection D a ≫ sequentialLevelColimitMap (𝟙 D) =
    sequentialLevelColimitInjection D a ≫ 𝟙 _
  rw [sequentialLevelColimitMap_fac]
  simp only [NatTrans.id_app, Category.id_comp, Category.comp_id]

/-- 概要：自然変換の合成の元の逐次段別余極限比較は、同じ実比較射の合成。
方針：同じ余極限の全注入後で元の比較の回収式を使う。
規約：成分ごとの比較と元の実注入を保持する。
使われ方：非連結化候補の hSp 比較の合成則。 -/
theorem sequentialLevelColimitMap_comp {D E F : SpectrumSequence.{u}}
    (η : D ⟶ E) (θ : E ⟶ F) :
    sequentialLevelColimitMap (η ≫ θ) =
      sequentialLevelColimitMap η ≫ sequentialLevelColimitMap θ := by
  apply (sequentialLevelColimitIsColimit D).hom_ext
  intro a
  change sequentialLevelColimitInjection D a ≫ sequentialLevelColimitMap (η ≫ θ) =
    sequentialLevelColimitInjection D a ≫ sequentialLevelColimitMap η ≫ sequentialLevelColimitMap θ
  rw [sequentialLevelColimitMap_fac, ← Category.assoc, sequentialLevelColimitMap_fac,
    Category.assoc, sequentialLevelColimitMap_fac]
  rfl

end SerrePositivity.KST.NonConnective
