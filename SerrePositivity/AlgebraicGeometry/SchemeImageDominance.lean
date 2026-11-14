module

public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
概要：実際のスキーム論的像への射の稠密性と、分離的な標的への射の一致を示す。
方針：像の affine 被覆上の切断の単射性と、閉じた等化子の核を使う。
規約：Stacks 01RH の射の一致。元の対象の被約性を要求しない。
使われ方：C06 の閉包から作った局所の射の貼り合わせ。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
universe u

/-- 準コンパクトな射の実際の像への射は scheme-theoretically dominant。 -/
theorem isSchemeTheoreticallyDominant_toImage
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] :
    IsSchemeTheoreticallyDominant f.toImage := by
  constructor
  apply Scheme.IdealSheafData.ext_of_iSup_eq_top
    (fun U : Y.affineOpens ↦ ⟨f.imageι ⁻¹ᵁ U.1, U.2.preimage f.imageι⟩)
    (f.imageι.iSup_preimage_eq_top (iSup_affineOpens_eq_top Y))
  intro U
  simp only [Scheme.Hom.ker_apply, Scheme.IdealSheafData.ideal_bot, Pi.bot_apply]
  exact (RingHom.injective_iff_ker_eq_bot _).mp (f.toImage_app_injective U)

/-- scheme-theoretically dominant な射上の一致は、分離的な標的への射の一致を反映する。 -/
theorem ext_of_isSchemeTheoreticallyDominant_of_isSeparated
    {X Y S W : Scheme.{u}} {f g : X ⟶ Y}
    (s : Y ⟶ S) [IsSeparated s] (h : f ≫ s = g ≫ s)
    (ι : W ⟶ X) [IsSchemeTheoreticallyDominant ι]
    (hU : ι ≫ f = ι ≫ g) : f = g := by
  let X' : Over S := Over.mk (f ≫ s)
  let Y' : Over S := Over.mk s
  let U' : Over S := Over.mk (ι ≫ f ≫ s)
  let f' : X' ⟶ Y' := Over.homMk f
  let g' : X' ⟶ Y' := Over.homMk g h.symm
  let ι' : U' ⟶ X' := Over.homMk ι
  haveI : IsSeparated Y'.hom := inferInstanceAs (IsSeparated s)
  have he : ι' ≫ f' = ι' ≫ g' := by ext1; exact hU
  let t := (equalizer.lift ι' he).left
  let e := (equalizer.ι f' g').left
  have hfac : t ≫ e = ι := by
    change (equalizer.lift ι' he ≫ equalizer.ι f' g').left = ι
    rw [equalizer.lift_ι]
    rfl
  haveI : IsClosedImmersion e := inferInstance
  have hk : e.ker ≤ ι.ker := by
    rw [← hfac]
    exact Scheme.Hom.le_ker_comp t e
  haveI : IsIso e := IsClosedImmersion.isIso_iff_ker_eq_bot.mpr
    (le_bot_iff.mp (by simpa only [ι.ker_eq_bot] using hk))
  rw [← cancel_epi e]
  congrm $(equalizer.condition f' g').left

end SerrePositivity.AlgebraicGeometry
