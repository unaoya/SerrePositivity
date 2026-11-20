module

public meta import SerrePositivity.Util.DeprecatedAlias
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

/-!
概要：Stacks 081T の strict transform に使う開部分スキームのスキーム論的像。
方針：像の閉埋め込みを元の開部分へ引き戻した射に切断を構成する。
規約：点集合の閉包とスキーム論的像を区別する。
使われ方：strict transform が元の開部分上で変化しないことの証明。
-/

@[expose] public noncomputable section

universe u
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits

set_option backward.isDefEq.respectTransparency false in
/--
概要：開部分スキームのスキーム論的像の閉包含は、その開部分上では同型。
方針：像への自然な射から引き戻しの切断を作り、閉埋め込みの単射性で逆性を示す。
規約：Stacks 081T、strict transform に必要な閉包の局所的な性質。
使われ方：開部分上で strict transform を元の空間と同定する。
-/
theorem openImageι_restrict_isIso {Y : Scheme.{u}} (U : Y.Opens) :
    IsIso (U.ι.imageι ∣_ U) := by
  let l : U.toScheme ⟶ pullback U.ι.imageι U.ι :=
    pullback.lift U.ι.toImage (𝟙 _) (by simp)
  have hl : l ≫ pullback.snd U.ι.imageι U.ι = 𝟙 _ := by simp [l]
  have hr : pullback.snd U.ι.imageι U.ι ≫ l = 𝟙 _ := by
    apply (cancel_mono (pullback.snd U.ι.imageι U.ι)).mp
    simp only [Category.assoc, hl, Category.comp_id, Category.id_comp]
  have : IsIso (pullback.snd U.ι.imageι U.ι) := ⟨⟨l, hr, hl⟩⟩
  unfold morphismRestrict
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/--
概要：U 上で同型な射を基底変更すると、U の逆像上でも同型。
方針：ファイバー積の制限正方形を作り、同型の基底変更を適用する。
規約：Stacks 081T、任意の基底変更に対して成立する。
使われ方：blowup 後の周辺ファイバー積が U 上で変化しないこと。
-/
theorem pullback_snd_restrict_isIso {X Y S : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) (U : S.Opens) [IsIso (f ∣_ U)] :
    IsIso (pullback.snd f g ∣_ g ⁻¹ᵁ U) := by
  have hpre : pullback.snd f g ⁻¹ᵁ g ⁻¹ᵁ U = pullback.fst f g ⁻¹ᵁ f ⁻¹ᵁ U := by
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, pullback.condition]
  have H := Scheme.Hom.isPullback_resLE (IsPullback.of_hasPullback f g)
    (US := U) (UT := g ⁻¹ᵁ U) (UX := f ⁻¹ᵁ U)
    (UY := pullback.snd f g ⁻¹ᵁ g ⁻¹ᵁ U) le_rfl le_rfl (by rw [hpre]; simp)
  have : IsIso (f.resLE U (f ⁻¹ᵁ U) le_rfl) := by
    rw [Scheme.Hom.resLE_eq_morphismRestrict]
    infer_instance
  simpa only [Scheme.Hom.resLE_eq_morphismRestrict] using H.isIso_snd_of_isIso

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
