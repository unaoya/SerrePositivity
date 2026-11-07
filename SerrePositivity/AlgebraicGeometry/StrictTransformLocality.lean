module

public import SerrePositivity.AlgebraicGeometry.StrictTransform
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-!
概要：狭義変換の構造射の平坦性を、ブローアップ基底の開被覆で判定する。
方針：準コンパクトな射のスキーム論的像は平坦基底変更と可換であることを使う。
規約：開部分の閉包はスキーム論的像として扱う。
使われ方：Stacks 0815 のアフィンチャート上の純変換を幾何学的な狭義変換に移す。
-/

@[expose] public noncomputable section

universe u v

namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits

set_option backward.isDefEq.respectTransparency false in
/--
概要：準コンパクトな射のスキーム論的像のイデアルは平坦基底変更と可換。
方針：像への射のスキーム論的支配性を平坦基底変更で保ち、像の閉包含の核を計算する。
規約：スキームの Noether 性は仮定しない。
使われ方：ブローアップの開チャートへの狭義変換の制限。
-/
theorem ker_pullback_snd_of_flat {X Y T : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f]
    (g : T ⟶ Y) [Flat g] :
    (pullback.snd f g).ker = f.ker.comap g := by
  let i := f.imageι
  let p := pullback.fst i g
  have hi : i.ker = f.ker := f.ker.ker_subschemeι
  have hf : IsSchemeTheoreticallyDominant f.toImage := by
    rw [isSchemeTheoreticallyDominant_iff]
    ext U : 2
    rw [f.toImage.ker_apply, Scheme.IdealSheafData.ideal_bot]
    exact (RingHom.injective_iff_ker_eq_bot _).mp
      (TopCat.Presheaf.app_injective_of_stalkFunctor_map_injective
        (F := f.image.sheaf) f.toImage.c U (fun x _ => f.stalkFunctor_toImage_injective x))
  have : Flat p := MorphismProperty.pullback_fst _ _ inferInstance
  let j := pullback.snd f.toImage p
  have hj : IsSchemeTheoreticallyDominant j := inferInstance
  have H := (IsPullback.of_hasPullback f.toImage p).paste_vert (IsPullback.of_hasPullback i g)
  rw [show f.toImage ≫ i = f from f.toImage_imageι] at H
  let e := H.isoIsPullback _ _ (IsPullback.of_hasPullback f g)
  rw [← Scheme.Hom.ker_comp_of_isIso e.hom,
    H.isoIsPullback_hom_snd _ _ (IsPullback.of_hasPullback f g),
    Scheme.Hom.ker_comp, show j.ker = ⊥ from j.ker_eq_bot, Scheme.IdealSheafData.map_bot]
  change (pullback.snd i g).ker = f.ker.comap g
  rw [← hi]
  -- 引き戻しの因子を入れ替え、閉埋め込みの核の公式を使う。
  rw [← Scheme.Hom.ker_comp_of_isIso (pullbackSymmetry g i).hom,
    pullbackSymmetry_hom_comp_snd]
  exact Scheme.IdealSheafData.ker_fst_of_isClosedImmersion i g

set_option backward.isDefEq.respectTransparency false in
/--
概要：準コンパクトな射のスキーム論的像と平坦基底変更の比較同型。
方針：二つの閉包含の核が一致することから、閉部分スキームを同定する。
規約：両辺の周辺空間は同じファイバー積。
使われ方：狭義変換の平坦性を開チャートに制限する。
-/
def imagePullbackIsoOfFlat {X Y T : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f]
    (g : T ⟶ Y) [Flat g] :
    (pullback.snd f g).image ≅ pullback f.imageι g := by
  let i := pullback.snd f.imageι g
  let j := (pullback.snd f g).imageι
  have h : i.ker = j.ker := by
    dsimp only [i, j]
    rw [ker_pullback_snd_of_flat f.imageι g, Scheme.IdealSheafData.ker_subschemeι,
      Scheme.IdealSheafData.ker_subschemeι, ker_pullback_snd_of_flat f g]
  letI := IsClosedImmersion.isIso_lift i j h
  exact asIso (IsClosedImmersion.lift i j h.le)

/-- 比較同型と周辺空間への閉包含の交換式。 -/
@[reassoc (attr := simp)]
theorem imagePullbackIsoOfFlat_hom_snd {X Y T : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f]
    (g : T ⟶ Y) [Flat g] :
    (imagePullbackIsoOfFlat f g).hom ≫ pullback.snd f.imageι g = (pullback.snd f g).imageι := by
  unfold imagePullbackIsoOfFlat
  exact IsClosedImmersion.lift_fac _ _ _

set_option backward.isDefEq.respectTransparency false in
private theorem ker_pullback_snd_opens_ι {Y T : Scheme.{u}}
    (W : Y.Opens) (g : T ⟶ Y) :
    (pullback.snd W.ι g).ker = (g ⁻¹ᵁ W).ι.ker := by
  calc
    _ = (pullback.fst g W.ι).ker := by
      rw [← Scheme.Hom.ker_comp_of_isIso (pullbackSymmetry W.ι g).hom,
        pullbackSymmetry_hom_comp_fst]
    _ = _ := by
      rw [← Scheme.Hom.ker_comp_of_isIso (pullbackRestrictIsoRestrict g W).inv,
        pullbackRestrictIsoRestrict_inv_fst]

set_option backward.isDefEq.respectTransparency false in
/--
概要：周辺スキームの同型を通じて、開部分のスキーム論的閉包の平坦性を移す。
方針：像の閉包含の基底変更を使い、同型による射の平坦性の不変性を適用する。
規約：開包含は準コンパクトとする。
使われ方：狭義変換を計算するアフィンチャートの座標環表示に移る。
-/
theorem flat_openImage_comp_iso_iff {Y T S : Scheme.{u}}
    (W : Y.Opens) [QuasiCompact W.ι] (e : T ≅ Y) (p : Y ⟶ S) :
    Flat ((e.hom ⁻¹ᵁ W).ι.imageι ≫ e.hom ≫ p) ↔ Flat (W.ι.imageι ≫ p) := by
  let k := pullback.fst W.ι.imageι e.hom
  let i := imagePullbackIsoOfFlat W.ι e.hom
  have h : (pullback.snd W.ι e.hom).imageι ≫ e.hom ≫ p = (i.hom ≫ k) ≫ W.ι.imageι ≫ p := by
    dsimp only [k, i]
    rw [Category.assoc, pullback.condition_assoc, imagePullbackIsoOfFlat_hom_snd_assoc]
  change Flat ((e.hom ⁻¹ᵁ W).ι.ker.subschemeι ≫ e.hom ≫ p) ↔ Flat (W.ι.imageι ≫ p)
  rw [← ker_pullback_snd_opens_ι]
  change Flat ((pullback.snd W.ι e.hom).imageι ≫ e.hom ≫ p) ↔ _
  rw [h, MorphismProperty.cancel_left_of_respectsIso @Flat]

set_option backward.isDefEq.respectTransparency false in
private theorem flat_openImage_comp_iff_of_openCover {Y S : Scheme.{u}}
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
  rw [ker_pullback_snd_opens_ι]

/-- Noether 基底上の固有射では、狭義変換の周辺空間も Noether。 -/
instance strictTransformAmbient_isNoetherian
    {X S : Scheme.{u}} [_root_.AlgebraicGeometry.IsNoetherian S]
    (f : X ⟶ S) [IsProper f] (J : S.IdealSheafData) :
    _root_.AlgebraicGeometry.IsNoetherian (strictTransformAmbient f J) := by
  let p : strictTransformAmbient f J ⟶ blowup J := pullback.snd f (blowupπ J)
  let : IsProper p := inferInstanceAs (IsProper (pullback.snd f (blowupπ J)))
  exact { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian p
          toCompactSpace := QuasiCompact.compactSpace_of_compactSpace p }

set_option backward.isDefEq.respectTransparency false in
/--
概要：狭義変換の平坦性は、ブローアップ基底の開被覆へ引き戻した開部分の閉包上で判定できる。
方針：開埋め込みは平坦なので、スキーム論的像と開チャートへの基底変更を交換する。
規約：基底は Noether、元の射は固有。これにより狭義変換を定める開包含は準コンパクト。
使われ方：標準チャート上で得た純変換の平坦性から狭義変換全体の平坦性を得る。
-/
theorem flat_strictTransformπ_iff_of_openCover
    {X S : Scheme.{u}} [_root_.AlgebraicGeometry.IsNoetherian S]
    (f : X ⟶ S) [IsProper f] (U : S.Opens) (J : S.IdealSheafData)
    (𝒰 : (blowup J).OpenCover.{v}) :
    Flat (strictTransformπ f U J) ↔ ∀ i, Flat
      ((pullback.fst (pullback.snd f (blowupπ J)) (𝒰.f i) ⁻¹ᵁ
        strictTransformOpen f U J).ι.imageι ≫
        pullback.snd (pullback.snd f (blowupπ J)) (𝒰.f i)) := by
  exact flat_openImage_comp_iff_of_openCover (strictTransformOpen f U J)
    (pullback.snd f (blowupπ J)) 𝒰

end SerrePositivity.AlgebraicGeometry
