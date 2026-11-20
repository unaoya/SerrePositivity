module

public meta import SerrePositivity.Util.DeprecatedAlias
public import SerrePositivity.AlgebraicGeometry.Flattening
public import SerrePositivity.AlgebraicGeometry.OpenImage

/-!
概要：Stacks 081T の blowup 支配に必要な strict transform の通常のスキームとしての構成。
方針：基底変更後の空間の U 上の開部分のスキーム論的像を取る。
規約：未証明の平坦化を仮定せず、対象と射をファイバー積と閉部分スキームで構成する。
使われ方：KST §5.2、Temkin 2008 Lemma 2.1.5 の Noether 特殊形。
-/

@[expose] public noncomputable section

universe u
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
variable {X S : Scheme.{u}} (f : X ⟶ S) (U : S.Opens) (J : S.IdealSheafData)

/--
概要：blowup 後の元の空間の基底変更。
方針：元の射と blowup 構造射のファイバー積を取る。
規約：Stacks 081T、まだ strict transform の閉部分スキームは取らない。
使われ方：strict transform の周辺空間。
-/
def strictTransformAmbient : Scheme := pullback f (blowupπ J)

/--
概要：基底変更後の空間の U 上の開部分。
方針：基底への合成射で U を引き戻す。
規約：Stacks 081T、通常の開部分スキーム。
使われ方：strict transform をスキーム論的閉包として定義する。
-/
def strictTransformOpen : (strictTransformAmbient f J).Opens :=
  (pullback.fst f (blowupπ J) ≫ f) ⁻¹ᵁ U

/--
概要：blowup による U に関する元の空間の strict transform。
方針：周辺空間内の U 上の開部分のスキーム論的像を取る。
規約：Stacks 081T、点集合だけの閉包で代用しない。
使われ方：平坦化を施す対象と blowup 支配の構成。
-/
def strictTransform : Scheme := (strictTransformOpen f U J).ι.image

/--
概要：strict transform の周辺ファイバー積への閉包含。
方針：スキーム論的像の包含射を用いる。
規約：Stacks 081T、閉部分スキーム構造を保持する。
使われ方：strict transform の固有性。
-/
def strictTransformι : strictTransform f U J ⟶ strictTransformAmbient f J :=
  (strictTransformOpen f U J).ι.imageι

set_option backward.isDefEq.respectTransparency false in
/--
概要：strict transform の周辺空間への包含は閉埋め込み。
方針：スキーム論的像の閉埋め込みを適用する。
規約：Stacks 081T、任意の元の射について成立する。
使われ方：strict transform の幾何学的性質の移送。
-/
instance strictTransformι_isClosedImmersion : IsClosedImmersion (strictTransformι f U J) := by
  unfold strictTransformι
  infer_instance

/--
概要：strict transform から blowup した基底への構造射。
方針：閉包含と周辺ファイバー積の第二射影を合成する。
規約：Stacks 081T、平坦化する射そのもの。
使われ方：固有性と、開部分スキームとなった後の全体との同定。
-/
def strictTransformπ : strictTransform f U J ⟶ blowup J :=
  strictTransformι f U J ≫ pullback.snd f (blowupπ J)

/--
概要：strict transform から元の空間への自然な射。
方針：閉包含と周辺ファイバー積の第一射影を合成する。
規約：Stacks 081T、支配射の候補。
使われ方：strict transform が基底に一致した後の blowup 支配射。
-/
def strictTransformToOriginal : strictTransform f U J ⟶ X :=
  strictTransformι f U J ≫ pullback.fst f (blowupπ J)

set_option backward.isDefEq.respectTransparency false in
/--
概要：strict transform の二つの構造射は元の基底上で可換。
方針：ファイバー積の交換式に閉包含を合成する。
規約：Stacks 081T、実際の射の等式。
使われ方：最終的な blowup 支配の因子化。
-/
@[reassoc] theorem strictTransform_square :
    strictTransformToOriginal f U J ≫ f = strictTransformπ f U J ≫ blowupπ J := by
  unfold strictTransformToOriginal strictTransformπ
  rw [Category.assoc, pullback.condition, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
/--
概要：元の射が固有なら strict transform の基底への射も固有。
方針：固有射の基底変更に閉埋め込みを合成する。
規約：Stacks 081T、平坦化の存在や Noether 性を仮定しない。
使われ方：strict transform が開部分スキームになった際の閉像性。
-/
instance strictTransformπ_isProper [IsProper f] : IsProper (strictTransformπ f U J) := by
  unfold strictTransformπ
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/--
概要：strict transform を作る開部分は blowup 側の U の逆像でもある。
方針：周辺ファイバー積の基底上の交換式を引き戻す。
規約：Stacks 081T、開集合の等式。
使われ方：strict transform の U 上の同型を構造射の制限に接続する。
-/
theorem strictTransformOpen_eq : strictTransformOpen f U J =
    pullback.snd f (blowupπ J) ⁻¹ᵁ blowupπ J ⁻¹ᵁ U := by
  unfold strictTransformOpen
  rw [pullback.condition, Scheme.Hom.comp_preimage]

set_option backward.isDefEq.respectTransparency false in
/--
概要：strict transform の周辺空間への包含は U 上の開部分では同型。
方針：開部分のスキーム論的像の一般的な局所同型を使う。
規約：Stacks 081T、元の射の固有性は不要。
使われ方：strict transform が U 上の元のデータを保持すること。
-/
theorem strictTransformι_restrict_isIso :
    IsIso (strictTransformι f U J ∣_ strictTransformOpen f U J) :=
  openImageι_restrict_isIso _

set_option backward.isDefEq.respectTransparency false in
/--
概要：元の射が U 上で同型なら strict transform の構造射も U の逆像上で同型。
方針：周辺の基底変更の同型と閉包の開部分上の同型を合成する。
規約：Stacks 081T、中心の admissible 性を追加仮定せず逆像開集合について述べる。
使われ方：平坦化後にも U 上の同型が保持されること。
-/
theorem strictTransformπ_restrict_isIso [IsIso (f ∣_ U)] :
    IsIso (strictTransformπ f U J ∣_ blowupπ J ⁻¹ᵁ U) := by
  have := pullback_snd_restrict_isIso f (blowupπ J) U
  have hι : IsIso (strictTransformι f U J ∣_
      pullback.snd f (blowupπ J) ⁻¹ᵁ blowupπ J ⁻¹ᵁ U) := by
    rw [← strictTransformOpen_eq]
    exact strictTransformι_restrict_isIso f U J
  unfold strictTransformπ
  rw [morphismRestrict_comp]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/--
概要：Noether 基底上の固有射の strict transform は Noether スキーム。
方針：blowup 後の基底の Noether 性と strict transform の固有性を使う。
規約：Stacks 081T、Noether 性を追加の入力として束ねない。
使われ方：strict transform の平坦化に必要な有限表示性と準コンパクト性。
-/
instance strictTransform_isNoetherian [_root_.AlgebraicGeometry.IsNoetherian S] [IsProper f] :
    _root_.AlgebraicGeometry.IsNoetherian (strictTransform f U J) where
  toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian (strictTransformπ f U J)
  toCompactSpace := QuasiCompact.compactSpace_of_compactSpace (strictTransformπ f U J)

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
