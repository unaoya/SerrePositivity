module

public import SerrePositivity.KST.Descent.SchemeFacts
public import SerrePositivity.AlgebraicGeometry.StrictTransform
public import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-!
# 補題 3.3 の有限全射の strict transform

## 概要
有限全射の strict transform は中心外の稠密性により有限全射となる。

## 方針
引き戻しへの閉包含から有限性、中心外の全射性と閉像性から全射性を得る。

## 規約
平坦化を達成する中心の存在はここでは結論しない。平坦性は実際の構造射について要求する。

## 使われ方
論文 補題 3.3 の平坦化 blowup から有限忠実平坦な細分を取り出す幾何学的段階。
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open SerrePositivity.AlgebraicGeometry

namespace SerrePositivity.KST.Descent

/-- 概要：固有射が稠密な開部分上で全射なら全体で全射（論文 補題 3.3）。
方針：開部分を像に含め、閉像性でその閉包も含める。
規約：開部分での同型性や基底の被約性は要求しない。
使われ方：有限な strict transform の全射性。 -/
theorem surjective_of_proper_dense_restrict {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsProper f] (U : Y.Opens) [Surjective (f ∣_ U)] (hU : Dense (U : Set Y)) :
    Surjective f := by
  have hsub : (U : Set Y) ⊆ Set.range f := by
    intro y hy
    obtain ⟨x, hx⟩ := (f ∣_ U).surjective ⟨y, hy⟩
    refine ⟨x.1, ?_⟩
    exact (congrArg (fun k => k x) (morphismRestrict_ι f U).symm).trans
      (congrArg U.ι hx)
  refine ⟨fun y ↦ ?_⟩
  exact closure_minimal hsub f.isClosedMap.isClosed_range (hU y)

variable {X S : Scheme.{u}} (f : X ⟶ S) (U : S.Opens) (J : S.IdealSheafData)

set_option backward.isDefEq.respectTransparency false in
/-- 概要：有限射の strict transform の構造射は有限（論文 補題 3.3）。
方針：有限射の底変換に実際の閉埋め込みを合成する。
規約：平坦性・全射性はこの有限性には不要。
使われ方：平坦化後の構造射を有限平坦射として扱う。 -/
theorem strictTransformπ_isFinite [IsFinite f] : IsFinite (strictTransformπ f U J) := by
  unfold strictTransformπ
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- 概要：全射の strict transform は元の開部分の逆像上で全射（論文 補題 3.3）。
方針：開部分上の閉包含の同型性と、全射の底変換・制限を合成する。
規約：中心外で元の射が同型になる仮定は課さない。
使われ方：稠密な中心外の全射性から全体の全射性を得る。 -/
theorem strictTransformπ_restrict_surjective [Surjective f] :
    Surjective (strictTransformπ f U J ∣_ blowupπ J ⁻¹ᵁ U) := by
  have hι : IsIso (strictTransformι f U J ∣_
      pullback.snd f (blowupπ J) ⁻¹ᵁ blowupπ J ⁻¹ᵁ U) := by
    rw [← strictTransformOpen_eq]
    exact strictTransformι_restrict_isIso f U J
  have : Surjective (pullback.snd f (blowupπ J) ∣_ blowupπ J ⁻¹ᵁ U) :=
    IsZariskiLocalAtTarget.restrict (P := @Surjective)
      (inferInstance : Surjective (pullback.snd f (blowupπ J))) _
  unfold strictTransformπ
  rw [morphismRestrict_comp]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- 概要：有限全射の strict transform は開部分の逆像が稠密なら全射（論文 補題 3.3）。
方針：有限性から固有性を得て、開部分での全射性と閉像性を使う。
規約：平坦化による降下や有限全射降下は仮定しない。
使われ方：admissible blowup の平坦化後の射の忠実性。 -/
theorem strictTransformπ_surjective_of_dense [IsFinite f] [Surjective f]
    (hd : Dense (blowupπ J ⁻¹ᵁ U).carrier) : Surjective (strictTransformπ f U J) := by
  have := strictTransformπ_isFinite f U J
  have := strictTransformπ_restrict_surjective f U J
  exact surjective_of_proper_dense_restrict (strictTransformπ f U J) _ hd

set_option backward.isDefEq.respectTransparency false in
/-- 概要：中心外から作った有限全射の strict transform は全射（論文 補題 3.3）。
方針：実際の blowup の中心外の稠密性を前の判定に適用する。
規約：中心は任意の実際のイデアル層で、平坦化の存在は別工程。
使われ方：中心外を使う平坦化から有限忠実平坦な細分へ接続する。 -/
theorem strictTransformπ_centerComplement_surjective [IsFinite f] [Surjective f] :
    Surjective (strictTransformπ f (centerComplement J) J) :=
  strictTransformπ_surjective_of_dense f (centerComplement J) J
    (blowup_centerComplement_dense J)

set_option backward.isDefEq.respectTransparency false in
/-- 概要：局所 Noether 基底上の有限射の strict transform は有限表示（論文 補題 3.3）。
方針：blowup の局所 Noether 性と有限射の有限型性を用いる。
規約：平坦化の存在や全射性を仮定しない。
使われ方：平坦化後の射の有限局所自由性に必要な有限表示性。 -/
theorem strictTransformπ_locallyOfFinitePresentation [IsLocallyNoetherian S] [IsFinite f] :
    LocallyOfFinitePresentation (strictTransformπ f U J) := by
  have : IsLocallyNoetherian (blowup J) :=
    LocallyOfFiniteType.isLocallyNoetherian (blowupπ J)
  have := strictTransformπ_isFinite f U J
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- 概要：中心外の有限全射の実際の strict transform が平坦なら有限忠実平坦な細分を得る（補題 3.3）。
方針：strict transform 自身、二つの指定射、有限性・全射性・有限表示性を返す。
規約：有限表示性のため基底を局所 Noether とする。平坦な中心の存在は別途証明する。
使われ方：平坦化の結論を有限忠実平坦な Čech 降下へ渡す。 -/
theorem exists_finiteFlat_refinement_of_flat_strictTransform
    [IsLocallyNoetherian S] [IsFinite f] [Surjective f]
    [Flat (strictTransformπ f (centerComplement J) J)] :
    ∃ (T : Scheme.{u}) (p : T ⟶ blowup J) (q : T ⟶ X),
      IsFinite p ∧ Flat p ∧ Surjective p ∧ LocallyOfFinitePresentation p ∧
        q ≫ f = p ≫ blowupπ J := by
  refine ⟨strictTransform f (centerComplement J) J,
    strictTransformπ f (centerComplement J) J,
    strictTransformToOriginal f (centerComplement J) J,
    strictTransformπ_isFinite f _ J, inferInstance,
    strictTransformπ_centerComplement_surjective f J,
    strictTransformπ_locallyOfFinitePresentation f _ J,
    strictTransform_square f _ J⟩

end SerrePositivity.KST.Descent
