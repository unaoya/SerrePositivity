module

public import SerrePositivity.AlgebraicGeometry.IdealSheafLocality
public import Mathlib.RingTheory.Finiteness.Ideal

/-!
概要：開被覆およびアフィン開の切断によるイデアル層の等式検出。
方針：既存のアフィン細分と開埋め込みの切断環同型を使う。
規約：実際の comap の等式。
使われ方：Stacks 01PF の有限型部分イデアル層の延長の貼り合わせ。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory
universe u

/-- 開被覆への逆像の一致は、元のイデアル層の一致を検出する。 -/
theorem idealSheaf_ext_of_openCover {X : Scheme.{u}} (𝒰 : X.OpenCover)
    {I J : X.IdealSheafData} (h : ∀ i, I.comap (𝒰.f i) = J.comap (𝒰.f i)) : I = J := by
  apply idealSheaf_ext_of_affineOpenCover 𝒰.affineRefinement
  intro i
  change I.comap ((𝒰.X i.1).affineCover.f i.2 ≫ 𝒰.f i.1) =
    J.comap ((𝒰.X i.1).affineCover.f i.2 ≫ 𝒰.f i.1)
  rw [Scheme.IdealSheafData.comap_comp, Scheme.IdealSheafData.comap_comp, h]

set_option backward.isDefEq.respectTransparency false in
/-- アフィン開への制限の全体切断イデアルを、既存の topIso で比較する。 -/
theorem idealSheaf_comap_opens_top {X : Scheme.{u}}
    (K : X.IdealSheafData) (U : X.affineOpens) :
    (K.comap U.1.ι).ideal ⟨⊤, isAffineOpen_top U⟩ =
      (K.ideal U).map U.1.topIso.inv.hom := by
  let V : X.affineOpens := ⟨U.1.ι ''ᵁ ⊤,
    (isAffineOpen_top U).image_of_isOpenImmersion U.1.ι⟩
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion, Scheme.Opens.ι_appIso]
  change K.ideal V = (K.ideal U).map U.1.topIso.inv.hom
  symm
  simpa [Scheme.Opens.topIso] using
    K.map_ideal' (U := V) (V := U) (eqToHom U.1.ι_image_top).op

set_option backward.isDefEq.respectTransparency false in
/-- アフィン開への逆像の一致は、その開上の切断イデアルの一致と同値。 -/
theorem idealSheaf_comap_eq_iff_affine_sections {X : Scheme.{u}}
    (I J : X.IdealSheafData) (U : X.affineOpens) :
    I.comap U.1.ι = J.comap U.1.ι ↔ I.ideal U = J.ideal U := by
  constructor
  · intro h
    have htop := congrArg
      (fun K : U.1.toScheme.IdealSheafData ↦ K.ideal ⟨⊤, isAffineOpen_top U⟩) h
    rw [idealSheaf_comap_opens_top, idealSheaf_comap_opens_top] at htop
    exact (Ideal.relIsoOfBijective U.1.topIso.inv.hom
      (ConcreteCategory.bijective_of_isIso U.1.topIso.inv)).symm.injective htop
  · intro h
    apply Scheme.IdealSheafData.ext_of_isAffine
    rw [idealSheaf_comap_opens_top, idealSheaf_comap_opens_top, h]

/-- アフィン開の制限の全体切断の有限生成性を元のアフィン切断へ戻す。 -/
theorem fg_ideal_of_comap_opens_top {X : Scheme.{u}}
    (K : X.IdealSheafData) (U : X.affineOpens)
    (h : ((K.comap U.1.ι).ideal ⟨⊤, isAffineOpen_top U⟩).FG) : (K.ideal U).FG := by
  rw [idealSheaf_comap_opens_top] at h
  have hmap := h.map U.1.topIso.hom.hom
  simpa only [Ideal.map_map, ← CommRingCat.hom_comp, Iso.inv_hom_id,
    CommRingCat.hom_id, Ideal.map_id] using hmap

end SerrePositivity.AlgebraicGeometry
