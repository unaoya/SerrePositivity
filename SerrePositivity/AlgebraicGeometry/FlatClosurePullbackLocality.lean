module

public import SerrePositivity.AlgebraicGeometry.FlatClosureDominantBaseChange
public import SerrePositivity.AlgebraicGeometry.OpenImage

/-!
概要：基底変更された固有射の、指定した開部分の閉包の平坦性の比較。
方針：二段の底変換を一段と比較し、共通細分と開被覆に沿う平坦性を扱う。
規約：閉包の準コンパクト性は Noether な試験スキームから得る。
使われ方：一般の固有全射の平坦化で局所ブローアップを大域化する。
-/

@[expose] public noncomputable section

namespace SerrePositivity.AlgebraicGeometry

open _root_.AlgebraicGeometry CategoryTheory Limits

/--
概要：底変換した射の、指定開集合の逆像の閉包が平坦である条件。
方針：開包含のスキーム論的像を底変換した射の始域の閉部分スキームとする。
規約：基底変更の写像は明示する。
使われ方：狭義変換の平坦性をブローアップ間の支配射に沿って比較する。
-/
def HasFlatOpenClosure {X S T : Scheme.{u}} (f : X ⟶ S) (U : S.Opens) (p : T ⟶ S) : Prop :=
  let q := pullback.snd f p
  Flat ((q ⁻¹ᵁ p ⁻¹ᵁ U).ι.imageι ≫ q)

set_option backward.isDefEq.respectTransparency false in
/--
概要：底変換後の開部分の閉包の平坦性は、二段の底変換でも合成での一段の底変換でも同じ。
方針：二つの周辺ファイバー積の標準同型を使う。
規約：最終基底は Noether とする。
使われ方：局所の平坦な狭義変換を、元の固有射の基底変更として扱う。
-/
theorem hasFlatOpenClosure_comp_iff {X S T V : Scheme.{u}}
    (f : X ⟶ S) [IsProper f] (U : S.Opens) (p : T ⟶ S) (g : V ⟶ T)
    [_root_.AlgebraicGeometry.IsNoetherian V] :
    HasFlatOpenClosure f U (g ≫ p) ↔ HasFlatOpenClosure (pullback.snd f p) (p ⁻¹ᵁ U) g := by
  let q := pullback.snd f p
  let q₁ := pullback.snd q g
  let q₂ := pullback.snd f (g ≫ p)
  let e := pullbackLeftPullbackSndIso f p g
  have he : e.hom ≫ q₂ = q₁ := pullbackLeftPullbackSndIso_hom_snd f p g
  let W := q₂ ⁻¹ᵁ (g ≫ p) ⁻¹ᵁ U
  let : _root_.AlgebraicGeometry.IsNoetherian (pullback f (g ≫ p)) :=
    { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian q₂
      toCompactSpace := QuasiCompact.compactSpace_of_compactSpace q₂ }
  have hW : e.hom ⁻¹ᵁ W = q₁ ⁻¹ᵁ g ⁻¹ᵁ p ⁻¹ᵁ U := by
    change e.hom ⁻¹ᵁ q₂ ⁻¹ᵁ (g ≫ p) ⁻¹ᵁ U = _
    rw [← Scheme.Hom.comp_preimage, he, Scheme.Hom.comp_preimage]
  have h := flat_openImage_comp_iso_iff W e q₂
  rw [hW, he] at h
  exact h.symm

set_option backward.isDefEq.respectTransparency false in
/--
概要：底変換後に境界開がスキーム論的稠密なら、支配射に沿って開部分の閉包の平坦性が保たれる。
方針：平坦な閉包を引き戻し、稠密性で引き戻し後の閉包と同定する。
規約：支配射の始域は Noether とする。
使われ方：局所の平坦化中心を支配する共通中心で、同じ平坦性を得る。
-/
theorem HasFlatOpenClosure.comp_of_dominant {X S T V : Scheme.{u}}
    {f : X ⟶ S} [IsProper f] {U : S.Opens} {p : T ⟶ S}
    (h : HasFlatOpenClosure f U p) (g : V ⟶ T)
    [_root_.AlgebraicGeometry.IsNoetherian V]
    [IsSchemeTheoreticallyDominant (g ⁻¹ᵁ p ⁻¹ᵁ U).ι] :
    HasFlatOpenClosure f U (g ≫ p) :=
  (hasFlatOpenClosure_comp_iff f U p g).mpr
    (flat_openImage_comp_pullback_of_flat_of_dominant (pullback.snd f p) (p ⁻¹ᵁ U) g h)

set_option backward.isDefEq.respectTransparency false in
/--
概要：許容ブローアップの狭義変換の平坦性を、底変換後の開部分の閉包の平坦性として読める。
方針：狭義変換を定める開集合を基底からの逆像で書く。
規約：元の射の固有性はこの比較に不要。
使われ方：局所の狭義変換を共通細分の平坦性に渡す。
-/
theorem hasFlatOpenClosure_blowup_iff {X S : Scheme.{u}} (f : X ⟶ S) (U : S.Opens)
    (J : S.IdealSheafData) :
    HasFlatOpenClosure f U (blowupπ J) ↔ Flat (strictTransformπ f U J) := by
  let q := pullback.snd f (blowupπ J)
  let P (W : (strictTransformAmbient f J).Opens) := Flat (W.ι.imageι ≫ q)
  change P (q ⁻¹ᵁ blowupπ J ⁻¹ᵁ U) ↔ P (strictTransformOpen f U J)
  rw [strictTransformOpen_eq]

end SerrePositivity.AlgebraicGeometry
