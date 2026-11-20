module

public import SerrePositivity.AlgebraicGeometry.FlatOpenImmersion
public import SerrePositivity.AlgebraicGeometry.BlowupSchemeDensity
public import SerrePositivity.AlgebraicGeometry.StrictTransformDomination

/-!
概要：Stacks 081T の平坦な strict transform から支配射へ至る段階。
方針：Noether 性による有限表示性、スキーム論的稠密性、平坦な射の開埋め込み判定を合わせる。
規約：平坦化を達成する中心の存在は、この段階の条件付き結論と区別する。
使われ方：有限型平坦化の構成を Noether blowup 支配の実際の因子化へ接続する。
-/

@[expose] public noncomputable section

universe u
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory
variable {X S : Scheme.{u}} (f : X ⟶ S) (U : S.Opens) (J : S.IdealSheafData)

set_option backward.isDefEq.respectTransparency false in
/--
概要：Noether 基底上で平坦な strict transform は、稠密な開部分上で同型なら開埋め込み。
方針：固有性から有限型性と分離性、Noether 性から有限表示性を得て平坦な射の判定を使う。
規約：Stacks 081S、081T。平坦化の存在そのものは別途構成する。
使われ方：平坦化された strict transform を基底の開部分スキームにする。
-/
theorem strictTransformπ_isOpenImmersion_of_flat_schematicallyDense
    [_root_.AlgebraicGeometry.IsNoetherian S] [IsProper f] [IsIso (f ∣_ U)]
    [IsSchemeTheoreticallyDominant (blowupπ J ⁻¹ᵁ U).ι]
    [Flat (strictTransformπ f U J)] : IsOpenImmersion (strictTransformπ f U J) := by
  have := strictTransformπ_restrict_isIso f U J
  exact isOpenImmersion_of_flat_iso_on_dense_open (strictTransformπ f U J) (blowupπ J ⁻¹ᵁ U)

set_option backward.isDefEq.respectTransparency false in
/--
概要：平坦な strict transform とスキーム論的稠密な開部分から実際の blowup 支配射を得る。
方針：開埋め込み性を導き、固有な開埋め込みの同型性と逆射を使う。
規約：Stacks 081T、結論は g と g≫f=π を返す。
使われ方：有限型平坦化を証明した後の最終的な因子化。
-/
theorem exists_domination_of_flat_schematicallyDense_strictTransform
    [_root_.AlgebraicGeometry.IsNoetherian S] [IsProper f] [IsIso (f ∣_ U)]
    [IsSchemeTheoreticallyDominant (blowupπ J ⁻¹ᵁ U).ι]
    [Flat (strictTransformπ f U J)] : ∃ g : blowup J ⟶ X, g ≫ f = blowupπ J := by
  have := strictTransformπ_isOpenImmersion_of_flat_schematicallyDense f U J
  have hd : Dense (blowupπ J ⁻¹ᵁ U).carrier := by
    have h := (blowupπ J ⁻¹ᵁ U).ι.denseRange
    change Dense (Set.range (blowupπ J ⁻¹ᵁ U).ι) at h
    rw [Scheme.Opens.range_ι] at h
    exact h
  exact exists_domination_of_strictTransform_open_dense f U J hd

set_option backward.isDefEq.respectTransparency false in
/--
概要：最初の admissible blowup の U の逆像包含はスキーム論的に稠密。
方針：中心補集合と U の一致を、blowup の中心外の零核へ適用する。
規約：Stacks 080Y Remark 38.30.1、081T の Noether 特殊形。
使われ方：平坦化の前に稠密性を整える。
-/
theorem initialAdmissibleBlowup_schematicallyDense [_root_.AlgebraicGeometry.IsNoetherian S] :
    IsSchemeTheoreticallyDominant (blowupπ (initialAdmissibleCenter U) ⁻¹ᵁ U).ι := by
  let J := initialAdmissibleCenter U
  have := blowup_centerComplement_isSchemeTheoreticallyDominant J
  have he : blowupπ J ⁻¹ᵁ centerComplement J = blowupπ J ⁻¹ᵁ U :=
    congrArg (fun V : S.Opens => blowupπ J ⁻¹ᵁ V) (initialAdmissibleCenter_complement U)
  rw [← Scheme.isoOfEq_inv_ι (blowup J) he]
  infer_instance

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
