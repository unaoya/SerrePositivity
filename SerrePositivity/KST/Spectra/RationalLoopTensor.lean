module

public import SerrePositivity.KST.Spectra.RationalSpectrumCocone
public import Mathlib.Algebra.Group.Equiv.TypeTags

/-!
概要：実際の loop telescope の整数次数群と有理テンソル積の同型。
方針：群の余極限を整数乗法の直極限へ移し、実証済みの局所化を使う。
規約：可換群の乗法記法を Additive で加法記法へ移してからテンソル積を取る。
使われ方：BF 1978 §2、HA §1.4.2。スペクトルの有理化の次数補正の前段階。
-/

@[expose] public section

universe u

open CategoryTheory Limits SSet
open scoped TensorProduct

namespace SerrePositivity.KST.Spectra.OmegaSpectrum

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：有理化のホモトピー群の cocone は群の圏でも余極限。
方針：集合での余極限性を群の忘却関手で反映する。
規約：AsSmall ℕ の filtered 図式。
使われ方：BF 1978 §2、HA §1.4.2。有理 telescope の群の計算。 -/
def rationalGroupCoconeIsColimit (X : OmegaSpectrum.{u}) (d : ℤ) :
    IsColimit (rationalGroupCocone X d) := by
  let : ReflectsColimit (spectrumHomotopyGroupDiagram (rationalDiagram X) d)
      (forget GrpCat.{u}) := reflectsColimit_of_reflectsIsomorphisms _ _
  exact isColimitOfReflects (forget GrpCat.{u}) (rationalGroupCoconeUnderlyingIsColimit X d)

/-- 概要：実際の有理化図式の整数次数群の余極限を有理テンソル積へ移す。
方針：余極限の一意性と整数乗法直極限の局所化を合成する。
規約：群の圏の同型として構成する。
使われ方：BF 1978 §2、HA §1.4.2。telescope のホモトピー群の実際の比較同型。 -/
def rationalGroupTensorIso (X : OmegaSpectrum.{u}) (d : ℤ) :
    colimit (spectrumHomotopyGroupDiagram (rationalDiagram X) d) ≅
      GrpCat.of (Multiplicative (rationalCoefficientGroup X d ⊗[ℤ] ℚ)) :=
  (colimit.isColimit _).coconePointUniqueUpToIso (rationalGroupCoconeIsColimit X d) ≪≫
    (AddEquiv.toMultiplicative
      (RationalTelescope.additiveLimitTensorEquiv
        (rationalCoefficientGroup X d)).toAddEquiv).toGrpIso

/-- 概要：実際の有理 loop telescope の整数次数群は元の loop 模型の群の有理化。
方針：filtered スペクトルの π_* 比較を群のテンソル積の比較へ合成する。
規約：全整数次数 d。
使われ方：BF 1978 §2、HA §1.4.2。有理化の対象の群の計算。 -/
def rationalLoopTensorEquiv (X : OmegaSpectrum.{u}) (d : ℤ) :
    homotopyGroup (rationalLoopTelescope X) d ≃*
      Multiplicative (rationalCoefficientGroup X d ⊗[ℤ] ℚ) :=
  Iso.groupIsoToMulEquiv
    ((filteredSpectrumHomotopyIso (rationalDiagram X) d).symm ≪≫ rationalGroupTensorIso X d)

/-- 概要：有理化の群の余極限比較は零段の元を a⊗1 へ送る。
方針：余極限の比較の脚での式と整数乗法直極限の零段の計算を使う。
規約：群の乗法表示を明示する。
使われ方：BF 1978 §2、HA §1.4.2。telescope の標準射の具体的な群の作用。 -/
theorem rationalGroupTensorIso_zero (X : OmegaSpectrum.{u}) (d : ℤ)
    (a : homotopyGroup (cotensor CirclePower.space.{u} X) d) :
    (rationalGroupTensorIso X d).hom.hom
      ((colimit.ι (spectrumHomotopyGroupDiagram (rationalDiagram X) d)
        (AsSmall.up.obj 0)).hom a) = Multiplicative.ofAdd (Additive.ofMul a ⊗ₜ[ℤ] (1 : ℚ)) := by
  have h := IsColimit.comp_coconePointUniqueUpToIso_hom
    (colimit.isColimit _) (rationalGroupCoconeIsColimit X d) (AsSmall.up.obj 0)
  have ha := DFunLike.congr_fun (congrArg GrpCat.Hom.hom h) a
  change Multiplicative.ofAdd ((RationalTelescope.additiveLimitTensorEquiv
    (rationalCoefficientGroup X d))
      (((colimit.isColimit _).coconePointUniqueUpToIso
        (rationalGroupCoconeIsColimit X d)).hom.hom
          ((colimit.ι (spectrumHomotopyGroupDiagram (rationalDiagram X) d)
            (AsSmall.up.obj 0)).hom a))) = _
  change ((colimit.isColimit
    (spectrumHomotopyGroupDiagram (rationalDiagram X) d)).coconePointUniqueUpToIso
      (rationalGroupCoconeIsColimit X d)).hom.hom
        ((colimit.ι (spectrumHomotopyGroupDiagram (rationalDiagram X) d)
          (AsSmall.up.obj 0)).hom a) = rationalGroupLeg X d 0 a at ha
  erw [ha]
  exact congrArg Multiplicative.ofAdd
    (RationalTelescope.additiveLimitTensorEquiv_zero
      (rationalCoefficientGroup X d) (Additive.ofMul a))


/-- 概要：有理 loop telescope の零段からの実際の射は群で a⊗1 を誘導する。
方針：filtered スペクトルの注入射を群の余極限の標準脚と比較する。
規約：比較は全整数次数で成り立つ。
使われ方：BF 1978 §2、HA §1.4.2。有理化の標準射の π_* の計算。 -/
theorem rationalLoopTensorEquiv_injection_zero (X : OmegaSpectrum.{u}) (d : ℤ)
    (a : homotopyGroup (cotensor CirclePower.space.{u} X) d) :
    rationalLoopTensorEquiv X d
      (homotopyMap (filteredSpectrumInjection (rationalDiagram X) (AsSmall.up.obj 0)) d a) =
        Multiplicative.ofAdd (Additive.ofMul a ⊗ₜ[ℤ] (1 : ℚ)) := by
  let D := spectrumHomotopyGroupDiagram (rationalDiagram X) d
  let e := filteredSpectrumHomotopyIso (rationalDiagram X) d
  have h : GrpCat.ofHom
      (homotopyMap (filteredSpectrumInjection (rationalDiagram X) (AsSmall.up.obj 0)) d) ≫
        e.inv = colimit.ι D (AsSmall.up.obj 0) := by
    rw [← filteredSpectrumHomotopyIso_ι]
    change colimit.ι D (AsSmall.up.obj 0) ≫ e.hom ≫ e.inv = _
    rw [Iso.hom_inv_id, Category.comp_id]
  have ha := DFunLike.congr_fun (congrArg GrpCat.Hom.hom h) a
  change (rationalGroupTensorIso X d).hom.hom (e.inv.hom
    (homotopyMap (filteredSpectrumInjection (rationalDiagram X) (AsSmall.up.obj 0)) d a)) = _
  have ha' : e.inv.hom
      (homotopyMap (filteredSpectrumInjection (rationalDiagram X) (AsSmall.up.obj 0)) d a) =
        (colimit.ι D (AsSmall.up.obj 0)).hom a := ha
  erw [ha']
  exact rationalGroupTensorIso_zero X d a

end

end SerrePositivity.KST.Spectra.OmegaSpectrum
