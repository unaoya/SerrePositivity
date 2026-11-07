module

public import SerrePositivity.AlgebraicGeometry.BlowupSchemeDensity
public import SerrePositivity.AlgebraicGeometry.StrictTransform
public import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-!
概要：固有全射の平坦な strict transform から、BS17 Lemma 2.6 の proper fppf 細分を取り出す。
方針：稠密な開集合上の像を確かめ、固有性による閉像性で全射性を得る。
規約：基底は Noether。平坦な strict transform を与える中心の存在は別途使う。
使われ方：Noether 平坦化を、固有全射の帰納レベルの証人に接続する。
-/

@[expose] public noncomputable section

universe u

namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits

private theorem surjective_of_dense_subset_range {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsProper f] {s : Set Y} (hs : Dense s) (h : s ⊆ Set.range f) : Surjective f := by
  let : IsDominant f := ⟨hs.mono h⟩
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/--
概要：Noether スキームの blowup で、基底の稠密開集合の逆像は稠密。
方針：中心外の逆像上で blowup 射は開写像となり、その部分はスキーム論的に稠密。
規約：基底の稠密開集合が中心と交わる場合も含む。
使われ方：strict transform の開部分の像から全射性を得る。
-/
theorem dense_preimage_blowupπ {S : Scheme.{u}} [_root_.AlgebraicGeometry.IsNoetherian S]
    (J : S.IdealSheafData) (U : S.Opens) (hU : Dense U.carrier) :
    Dense (blowupπ J ⁻¹ᵁ U).carrier := by
  let V := centerComplement J
  let W := blowupπ J ⁻¹ᵁ V
  have := blowupπ_restrict_complement_isIso J
  have hOpen : IsOpenMap (W.ι ≫ blowupπ J) := by
    rw [← morphismRestrict_ι]
    exact V.ι.isOpenEmbedding.isOpenMap.comp (blowupπ J ∣_ V).homeomorph.isOpenMap
  exact W.ι.denseRange.dense_of_mapsTo W.ι.continuous (hU.preimage hOpen)
    (fun _ hx => hx)

set_option backward.isDefEq.respectTransparency false in
/--
概要：固有全射の strict transform は、blowup 基底上で元の開集合の逆像が稠密なら全射。
方針：稠密開上の点を周辺ファイバー積で持ち上げ、開包含のスキーム論的像を経由させる。
規約：稠密性は位相的な意味。strict transform の平坦性はこの補題には不要。
使われ方：平坦化で得た固有な strict transform が proper fppf になることを示す。
-/
theorem strictTransformπ_surjective_of_dense {X S : Scheme.{u}} (f : X ⟶ S)
    [IsProper f] [Surjective f] (U : S.Opens) (J : S.IdealSheafData)
    (hU : Dense (blowupπ J ⁻¹ᵁ U).carrier) : Surjective (strictTransformπ f U J) := by
  apply surjective_of_dense_subset_range (strictTransformπ f U J) hU
  intro y hy
  obtain ⟨x, hx⟩ := (pullback.snd f (blowupπ J)).surjective y
  have hxU : x ∈ strictTransformOpen f U J := by
    rw [strictTransformOpen_eq]
    change pullback.snd f (blowupπ J) x ∈ (blowupπ J ⁻¹ᵁ U)
    rwa [hx]
  let V := strictTransformOpen f U J
  refine ⟨V.ι.toImage ⟨x, hxU⟩, ?_⟩
  change (V.ι.toImage ≫ strictTransformπ f U J) ⟨x, hxU⟩ = y
  rw [strictTransformπ, ← Category.assoc]
  change ((V.ι.toImage ≫ V.ι.imageι) ≫ pullback.snd f (blowupπ J)) ⟨x, hxU⟩ = y
  rw [Scheme.Hom.toImage_imageι]
  exact hx

set_option backward.isDefEq.respectTransparency false in
/--
概要：Noether 基底上の固有全射に平坦な strict transform があれば、稠密開を保つ
blowup と proper fppf 射で細分できる。
方針：両方の射の固有性を使って、稠密開上の像を基底全体へ広げる。
規約：proper fppf は固有・平坦・全射・局所有限表示の条件として返す。
使われ方：BS17 Lemma 2.6 の正次元の場合に、平坦化中心から細分を作る。
-/
theorem exists_proper_fppf_blowup_refinement_of_flat_strictTransform
    {X S : Scheme.{u}} [_root_.AlgebraicGeometry.IsNoetherian S] (f : X ⟶ S)
    [IsProper f] [Surjective f] (U : S.Opens) (J : S.IdealSheafData)
    (hU : Dense U.carrier) (hJ : IsUAdmissibleCenter U J)
    [Flat (strictTransformπ f U J)] :
    IsProper (blowupπ J) ∧ Surjective (blowupπ J) ∧ IsIso (blowupπ J ∣_ U) ∧
      ∃ (X' : Scheme.{u}) (g : X' ⟶ blowup J) (k : X' ⟶ X),
        IsProper g ∧ Flat g ∧ Surjective g ∧ LocallyOfFinitePresentation g ∧
          k ≫ f = g ≫ blowupπ J := by
  have hIso := blowupπ_restrict_admissible_isIso U J hJ
  have hSurj : Surjective (blowupπ J) := by
    apply surjective_of_dense_subset_range (blowupπ J) hU
    intro y hy
    obtain ⟨x, hx⟩ := (blowupπ J ∣_ U).surjective ⟨y, hy⟩
    refine ⟨x.1, ?_⟩
    calc
      blowupπ J x.1 = ((blowupπ J ⁻¹ᵁ U).ι ≫ blowupπ J) x := rfl
      _ = ((blowupπ J ∣_ U) ≫ U.ι) x :=
        congrArg (fun h => h x) (morphismRestrict_ι (blowupπ J) U).symm
      _ = y := congrArg U.ι hx
  have hStrict := strictTransformπ_surjective_of_dense f U J (dense_preimage_blowupπ J U hU)
  exact ⟨inferInstance, hSurj, hIso, strictTransform f U J, strictTransformπ f U J,
    strictTransformToOriginal f U J, inferInstance, inferInstance, hStrict, inferInstance,
    strictTransform_square f U J⟩

end SerrePositivity.AlgebraicGeometry
