module

public import SerrePositivity.AlgebraicGeometry.SchemeAffinePullbackSections

/-!
概要：実際の底変換のアフィン切断の比較を、開集合の制限に自然にする。
方針：pushout の二つの入射上で、構造層の appLE の合成を検査する。
規約：平坦性を加えず、canonical な pushoutSection の同じ同型を使う。
使われ方：有限交叉の図式全体での底変換と閉厚化の比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
universe u
variable {X Y S T : Scheme.{u}} {f : T ⟶ S} {g : Y ⟶ X} {iX : X ⟶ S} {iY : Y ⟶ T}
variable (H : IsPullback g iY iX f)
variable {US : S.Opens} {UT : T.Opens} {UX UX' : X.Opens} {UY UY' : Y.Opens}
variable (hUST : UT ≤ f ⁻¹ᵁ US) (hUSX : UX ≤ iX ⁻¹ᵁ US)
variable (hUY : UY = g ⁻¹ᵁ UX ⊓ iY ⁻¹ᵁ UT)
variable (hUY' : UY' = g ⁻¹ᵁ UX' ⊓ iY ⁻¹ᵁ UT) (hsmall : UX' ≤ UX)
variable (hUS : IsAffineOpen US) (hUT : IsAffineOpen UT)
variable (hUX : IsAffineOpen UX) (hUX' : IsAffineOpen UX')

/-- 底変換の canonical なアフィン切断の比較は、開集合を狭める制限に自然。 -/
theorem schemeAffinePullbackSectionIso_naturality :
    pushout.map (iX.appLE US UX hUSX) (f.appLE US UT hUST)
        (iX.appLE US UX' (hsmall.trans hUSX)) (f.appLE US UT hUST)
        (X.presheaf.map (homOfLE hsmall).op) (𝟙 _) (𝟙 _)
        (by simp only [Category.id_comp, Scheme.Hom.appLE_map])
        (by simp only [Category.comp_id, Category.id_comp]) ≫
        (schemeAffinePullbackSectionIso H hUST (hsmall.trans hUSX) hUY' hUS hUT hUX').hom =
      (schemeAffinePullbackSectionIso H hUST hUSX hUY hUS hUT hUX).hom ≫
        Y.presheaf.map (homOfLE (show UY' ≤ UY from by
          rw [hUY, hUY']
          exact inf_le_inf (g.preimage_mono hsmall) le_rfl)).op := by
  apply pushout.hom_ext
  · simp only [Category.assoc, pushout.map, pushout.inl_desc_assoc,
      schemeAffinePullbackSectionIso_inl, schemeAffinePullbackSectionIso_inl_assoc,
      Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]
  · simp only [Category.assoc, pushout.map, pushout.inr_desc_assoc,
      schemeAffinePullbackSectionIso_inr, schemeAffinePullbackSectionIso_inr_assoc,
      Category.id_comp, Scheme.Hom.appLE_map]

end SerrePositivity.AlgebraicGeometry
