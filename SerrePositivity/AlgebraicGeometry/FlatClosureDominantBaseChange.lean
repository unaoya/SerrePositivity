module

public import SerrePositivity.AlgebraicGeometry.StrictTransformLocality

/-!
概要：平坦化した開部分の閉包を、境界がスキーム論的稠密な細分へ引き戻す。
方針：平坦な閉包の底変換上でも境界は稠密なので、その閉部分スキームが引き戻し後の閉包になる。
規約：底変換そのものの平坦性は仮定しない。
使われ方：局所平坦化したブローアップを共通の大域ブローアップで支配する。
-/

@[expose] public noncomputable section

namespace SerrePositivity.AlgebraicGeometry

open _root_.AlgebraicGeometry CategoryTheory Limits

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 3200000 in
-- 二つの閉部分スキームの核とアフィン引き戻しの構造を照合する。
/--
概要：基底の開部分の逆像の閉包が平坦なら、境界開がスキーム論的稠密な底変換後も閉包が平坦。
方針：平坦な閉包を底変換し、境界開の逆像がその中でスキーム論的に稠密となることから閉包の核を比較する。
規約：底変換先の境界開の包含は準コンパクトとする。
使われ方：許容中心を共通細分したとき、狭義変換の平坦性を移す。
-/
theorem flat_openImage_comp_pullback_of_flat_of_dominant
    {Y S T : Scheme.{u}} (p : Y ⟶ S) (U : S.Opens) (g : T ⟶ S)
    [QuasiCompact (g ⁻¹ᵁ U).ι] [IsSchemeTheoreticallyDominant (g ⁻¹ᵁ U).ι]
    (hf : Flat ((p ⁻¹ᵁ U).ι.imageι ≫ p)) :
    Flat (((pullback.snd p g) ⁻¹ᵁ (g ⁻¹ᵁ U)).ι.imageι ≫ pullback.snd p g) := by
  let W := p ⁻¹ᵁ U
  let Q := pullback p g
  let q := pullback.snd p g
  let r := pullback.fst p g
  let V := q ⁻¹ᵁ (g ⁻¹ᵁ U)
  let H := pullback W.ι.imageι r
  let i : H ⟶ Q := pullback.snd W.ι.imageι r
  have hi : IsPullback (pullback.fst W.ι.imageι r) (i ≫ q) (W.ι.imageι ≫ p) g :=
    (IsPullback.of_hasPullback W.ι.imageι r).paste_vert (IsPullback.of_hasPullback p g)
  let : Flat (i ≫ q) := MorphismProperty.of_isPullback hi hf
  have hV : r ⁻¹ᵁ W = V := by
    change r ⁻¹ᵁ p ⁻¹ᵁ U = q ⁻¹ᵁ g ⁻¹ᵁ U
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, pullback.condition]
  let e := pullbackRestrictIsoRestrict r W
  let k := (Q.isoOfEq hV).inv ≫ e.inv
  have hk : k ≫ pullback.fst r W.ι = V.ι := by
    rw [Category.assoc, pullbackRestrictIsoRestrict_inv_fst, Scheme.isoOfEq_inv_ι]
  have hm₀ : (k ≫ pullback.snd r W.ι ≫ W.ι.toImage) ≫ W.ι.imageι = V.ι ≫ r := by
    calc
      _ = k ≫ pullback.snd r W.ι ≫ W.ι := by
        simp only [Category.assoc, Scheme.Hom.toImage_imageι]
      _ = (k ≫ pullback.fst r W.ι) ≫ r := by
        rw [Category.assoc k]
        exact congrArg (k ≫ ·) (pullback.condition (f := r) (g := W.ι)).symm
      _ = _ := by rw [hk]
  let m := pullback.lift (k ≫ pullback.snd r W.ι ≫ W.ι.toImage) V.ι hm₀
  have hm : m ≫ i = V.ι := pullback.lift_snd _ _ _
  have hdom : IsSchemeTheoreticallyDominant (i ⁻¹ᵁ V).ι := by
    rw [show i ⁻¹ᵁ V = (i ≫ q) ⁻¹ᵁ (g ⁻¹ᵁ U) from (Scheme.Hom.comp_preimage ..).symm]
    exact IsSchemeTheoreticallyDominant.of_isPullback
      (isPullback_morphismRestrict (i ≫ q) (g ⁻¹ᵁ U))
  have hr : (i ∣_ V) ≫ m = (i ⁻¹ᵁ V).ι := by
    apply (cancel_mono i).mp
    rw [Category.assoc, hm, morphismRestrict_ι]
  have hmker : m.ker = ⊥ := by
    apply le_antisymm _ bot_le
    exact ((i ∣_ V).le_ker_comp m).trans_eq (hr ▸ hdom.ker_eq_bot)
  have hker : i.ker = V.ι.imageι.ker := by
    rw [Scheme.IdealSheafData.ker_subschemeι, ← hm, Scheme.Hom.ker_comp, hmker,
      Scheme.IdealSheafData.map_bot]
  let l : H ⟶ V.ι.image := IsClosedImmersion.lift V.ι.imageι i hker.ge
  let : IsIso l := IsClosedImmersion.isIso_lift V.ι.imageι i hker.symm
  change Flat (V.ι.imageι ≫ q)
  have hl : l ≫ V.ι.imageι = i := IsClosedImmersion.lift_fac _ _ _
  apply (MorphismProperty.cancel_left_of_respectsIso @Flat l (V.ι.imageι ≫ q)).mp
  rw [← Category.assoc l, hl]
  infer_instance

end SerrePositivity.AlgebraicGeometry
