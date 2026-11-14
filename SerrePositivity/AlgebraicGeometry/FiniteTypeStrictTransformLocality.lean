module

public import SerrePositivity.AlgebraicGeometry.StrictTransformLocality

/-!
概要：狭義変換の局所性を、固有性を仮定せず有限型射へ供給する。
方針：周辺空間の Noether 性を局所有限型性と準コンパクト性から得る。
規約：既存の固有射用の宣言を変更せず、新しい入口を使う。
使われ方：Rydh 3.10 の有限表示射の平坦化。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry
universe u v

/-- 開包含の pullback の核は、実際の逆像開包含の核。 -/
theorem ker_pullback_openInclusion {Y T : Scheme.{u}} (W : Y.Opens) (g : T ⟶ Y) :
    (pullback.snd W.ι g).ker = (g ⁻¹ᵁ W).ι.ker := by
  calc
    _ = (pullback.fst g W.ι).ker := by
      rw [← Scheme.Hom.ker_comp_of_isIso (pullbackSymmetry W.ι g).hom,
        pullbackSymmetry_hom_comp_fst]
    _ = _ := by
      rw [← Scheme.Hom.ker_comp_of_isIso (pullbackRestrictIsoRestrict g W).inv,
        pullbackRestrictIsoRestrict_inv_fst]

set_option backward.isDefEq.respectTransparency false in
/-- 準コンパクトな開部分の像の構造射の平坦性は、終域の開被覆上で判定できる。 -/
theorem flat_openImage_iff_on_targetCover {Y S : Scheme.{u}}
    (W : Y.Opens) [QuasiCompact W.ι] (p : Y ⟶ S) (𝒰 : S.OpenCover.{v}) :
    Flat (W.ι.imageι ≫ p) ↔ ∀ i, Flat
      ((pullback.fst p (𝒰.f i) ⁻¹ᵁ W).ι.imageι ≫ pullback.snd p (𝒰.f i)) := by
  rw [IsZariskiLocalAtTarget.iff_of_openCover (P := @Flat) 𝒰]
  refine forall_congr' fun i => ?_
  let g := 𝒰.f i
  let r := pullback.fst p g
  let q := pullback.snd p g
  let e := imagePullbackIsoOfFlat W.ι r
  have H := (IsPullback.of_hasPullback W.ι.imageι r).paste_vert
    (IsPullback.of_hasPullback p g)
  let e' := H.isoIsPullback _ _ (IsPullback.of_hasPullback (W.ι.imageι ≫ p) g)
  have hcomp : (e ≪≫ e').hom ≫ pullback.snd (W.ι.imageι ≫ p) g =
      (pullback.snd W.ι r).imageι ≫ q := by
    rw [Iso.trans_hom, Category.assoc,
      H.isoIsPullback_hom_snd _ _ (IsPullback.of_hasPullback (W.ι.imageι ≫ p) g)]
    exact imagePullbackIsoOfFlat_hom_snd_assoc W.ι r q
  change Flat (pullback.snd (W.ι.imageι ≫ p) g) ↔ Flat ((r ⁻¹ᵁ W).ι.imageι ≫ q)
  rw [← MorphismProperty.cancel_left_of_respectsIso @Flat (e ≪≫ e').hom, hcomp]
  change Flat ((pullback.snd W.ι r).ker.subschemeι ≫ q) ↔
    Flat ((r ⁻¹ᵁ W).ι.ker.subschemeι ≫ q)
  rw [ker_pullback_openInclusion]

/-- 有限型射の狭義変換の周辺空間は、Noether 基底上で Noether。 -/
theorem strictTransformAmbient_noetherian_of_finiteType
    {X S : Scheme.{u}} [_root_.AlgebraicGeometry.IsNoetherian S]
    (f : X ⟶ S) [LocallyOfFiniteType f] [QuasiCompact f] (J : S.IdealSheafData) :
    _root_.AlgebraicGeometry.IsNoetherian (strictTransformAmbient f J) := by
  let p : strictTransformAmbient f J ⟶ blowup J := pullback.snd f (blowupπ J)
  letI : LocallyOfFiniteType p := inferInstanceAs (LocallyOfFiniteType (pullback.snd f (blowupπ J)))
  letI : QuasiCompact p := inferInstanceAs (QuasiCompact (pullback.snd f (blowupπ J)))
  exact { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian p
          toCompactSpace := QuasiCompact.compactSpace_of_compactSpace p }

/-- 有限型射の狭義変換の平坦性は、blowup 基底の開被覆上で判定できる。 -/
theorem flat_strictTransformπ_iff_of_openCover_of_finiteType
    {X S : Scheme.{u}} [_root_.AlgebraicGeometry.IsNoetherian S]
    (f : X ⟶ S) [LocallyOfFiniteType f] [QuasiCompact f]
    (U : S.Opens) (J : S.IdealSheafData) (𝒰 : (blowup J).OpenCover.{v}) :
    Flat (strictTransformπ f U J) ↔ ∀ i, Flat
      ((pullback.fst (pullback.snd f (blowupπ J)) (𝒰.f i) ⁻¹ᵁ
        strictTransformOpen f U J).ι.imageι ≫
        pullback.snd (pullback.snd f (blowupπ J)) (𝒰.f i)) := by
  letI := strictTransformAmbient_noetherian_of_finiteType f J
  exact flat_openImage_iff_on_targetCover (strictTransformOpen f U J)
    (pullback.snd f (blowupπ J)) 𝒰

end SerrePositivity.AlgebraicGeometry
