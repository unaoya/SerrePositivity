module

public import SerrePositivity.AlgebraicGeometry.StrictTransform
public import SerrePositivity.AlgebraicGeometry.ProperOpenIso

/-!
概要：Stacks 081T の strict transform から blowup 支配射を取り出す最後の段階。
方針：固有な開埋め込みを稠密な開部分での同型から全体の同型とし、その逆射を合成する。
規約：strict transform の開埋め込み性を証明する平坦化の段階とは区別する。
使われ方：KST §5.2、Temkin 2008 Lemma 2.1.5 の実際の因子化。
-/

@[expose] public noncomputable section

universe u
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory
variable {X S : Scheme.{u}} (f : X ⟶ S) (U : S.Opens) (J : S.IdealSheafData)

set_option backward.isDefEq.respectTransparency false in
/--
概要：strict transform が固有な開部分スキームなら、稠密な U 上の同型から基底全体に一致する。
方針：固有な開埋め込みの一般的な同型判定を適用する。
規約：Stacks 081T Lemma 38.31.4 の最後の段階。平坦化の存在はここでは主張しない。
使われ方：平坦化を証明した後に支配射を構成する。
-/
theorem strictTransformπ_isIso_of_open_dense [IsProper f] [IsIso (f ∣_ U)]
    [IsOpenImmersion (strictTransformπ f U J)]
    (hd : Dense (blowupπ J ⁻¹ᵁ U).carrier) : IsIso (strictTransformπ f U J) := by
  have := strictTransformπ_restrict_isIso f U J
  exact isIso_of_proper_openImmersion_dense_restrict (strictTransformπ f U J) _ hd

set_option backward.isDefEq.respectTransparency false in
/--
概要：同型となった strict transform から元の固有射を支配する実際の因子化射を構成する。
方針：strict transform の構造射の逆と元の空間への射を合成する。
規約：Stacks 081T、結論は実際の g と構造射の等式を返す。
使われ方：Noether 特殊形の支配定理の最終的な射の構成。
-/
theorem exists_domination_of_strictTransform_isIso [IsIso (strictTransformπ f U J)] :
    ∃ g : blowup J ⟶ X, g ≫ f = blowupπ J := by
  refine ⟨inv (strictTransformπ f U J) ≫ strictTransformToOriginal f U J, ?_⟩
  rw [Category.assoc, strictTransform_square, IsIso.inv_hom_id_assoc]

set_option backward.isDefEq.respectTransparency false in
/--
概要：稠密な U 上で同型な固有な strict transform が開埋め込みなら blowup 支配射が得られる。
方針：構造射を同型と判定し、その逆を用いて因子化を構成する。
規約：Stacks 081T の最後の二段階。開埋め込み性を与える平坦化自体は別途証明する。
使われ方：平坦化の結論を支配の存在へ接続する。
-/
theorem exists_domination_of_strictTransform_open_dense [IsProper f] [IsIso (f ∣_ U)]
    [IsOpenImmersion (strictTransformπ f U J)]
    (hd : Dense (blowupπ J ⁻¹ᵁ U).carrier) :
    ∃ g : blowup J ⟶ X, g ≫ f = blowupπ J := by
  have := strictTransformπ_isIso_of_open_dense f U J hd
  exact exists_domination_of_strictTransform_isIso f U J

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
