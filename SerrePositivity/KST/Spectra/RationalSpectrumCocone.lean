module

public import SerrePositivity.KST.Spectra.RationalSpectrumDiagram
public import SerrePositivity.KST.Spectra.RationalGroupTelescope
public import SerrePositivity.KST.Spectra.FilteredSpectrumHomotopy

/-!
概要：実際のスペクトルの有理 telescope のホモトピー群の余極限。
方針：整数次数の遷移を実証済みの整数乗法の直極限へ送る。
規約：乗法表示の可換群に Additive を施して ℤ 加群の直極限を使う。
使われ方：BF 1978 §2、HA §1.4.2。有理化の群のテンソル積との比較。
-/

@[expose] public section

universe u

open CategoryTheory Limits SSet

namespace SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace RationalTelescope

/-- 概要：整数乗法の遷移は乗法表示へ戻すと区間係数の冪。
方針：自然数の整数作用と nsmul の一致、および Additive の冪の式を使う。
規約：G は任意の可換群。
使われ方：HA §1.4.2。スペクトルの遷移と加法群の直極限の照合。 -/
theorem scalarTransition_ofMul {G : Type u} [CommGroup G] (i l : ℕ) (hil : i ≤ l) (a : G) :
    scalarTransition (Additive G) i l hil (Additive.ofMul a) =
      Additive.ofMul (a ^ coefficient i l) := by
  change (coefficient i l : ℤ) • Additive.ofMul a = _
  simp only [natCast_zsmul, ofMul_pow]

end RationalTelescope

namespace OmegaSpectrum

/-- 概要：loop cotensor の整数次数群の加法表示。
方針：実証済みの可換群を Additive で包む。
規約：群の元や群構造を変更せず表記だけを変える。
使われ方：HA §1.4.2。有理化の ℤ 加群の直極限。 -/
abbrev rationalCoefficientGroup (X : OmegaSpectrum.{u}) (d : ℤ) :=
  Additive (homotopyGroup (cotensor CirclePower.space.{u} X) d)

/-- 概要：有理化図式の各段から加法直極限への群準同型。
方針：Additive と Multiplicative の間で線形な標準射を読む。
規約：i は自然数の段。
使われ方：BF 1978 §2、HA §1.4.2。群の余極限 cocone の脚。 -/
def rationalGroupLeg (X : OmegaSpectrum.{u}) (d : ℤ) (i : ℕ) :
    homotopyGroup (cotensor CirclePower.space.{u} X) d →*
      Multiplicative (RationalTelescope.additiveLimit (rationalCoefficientGroup X d)) where
  toFun a := Multiplicative.ofAdd
    (RationalTelescope.inclusion (rationalCoefficientGroup X d) i (Additive.ofMul a))
  map_one' := by
    change RationalTelescope.inclusion (rationalCoefficientGroup X d) i 0 = 0
    exact map_zero _
  map_mul' a b := by
    change RationalTelescope.inclusion (rationalCoefficientGroup X d) i
        (Additive.ofMul a + Additive.ofMul b) =
      RationalTelescope.inclusion (rationalCoefficientGroup X d) i (Additive.ofMul a) +
        RationalTelescope.inclusion (rationalCoefficientGroup X d) i (Additive.ofMul b)
    exact map_add _ _ _

/-- 概要：実際の有理化図式の整数次数群から加法直極限への cocone。
方針：遷移の冪の式を整数乗法の直極限の関係へ移す。
規約：対象の圏は群の圏。
使われ方：BF 1978 §2、HA §1.4.2。telescope のホモトピー群の余極限。 -/
def rationalGroupCocone (X : OmegaSpectrum.{u}) (d : ℤ) :
    Cocone (spectrumHomotopyGroupDiagram (rationalDiagram X) d) where
  pt := GrpCat.of
    (Multiplicative (RationalTelescope.additiveLimit (rationalCoefficientGroup X d)))
  ι := {
    app i := GrpCat.ofHom (rationalGroupLeg X d (AsSmall.down.obj i))
    naturality i l f := by
      ext a
      change homotopyGroup (cotensor CirclePower.space.{u} X) d at a
      change rationalGroupLeg X d (AsSmall.down.obj l)
          (homotopyMap ((rationalDiagram X).map f) d a) =
        rationalGroupLeg X d (AsSmall.down.obj i) a
      rw [rationalDiagram_homotopyMap]
      change RationalTelescope.inclusion (rationalCoefficientGroup X d) (AsSmall.down.obj l)
          (Additive.ofMul (a ^ RationalTelescope.coefficient
            (AsSmall.down.obj i) (AsSmall.down.obj l))) = _
      erw [← RationalTelescope.scalarTransition_ofMul _ _ (leOfHom f.down)]
      exact RationalTelescope.inclusion_transition _ (leOfHom f.down) _ }

/-- 概要：有理化の群の cocone は underlying 集合でも余極限。
方針：直極限の代表の存在と等式の後続段での検出を使う。
規約：AsSmall による添字の拡大は元と等式の検出を変えない。
使われ方：BF 1978 §2、HA §1.4.2。群の圏の余極限性の検査。 -/
def rationalGroupCoconeUnderlyingIsColimit (X : OmegaSpectrum.{u}) (d : ℤ) :
    IsColimit ((forget GrpCat.{u}).mapCocone (rationalGroupCocone X d)) := by
  refine Types.FilteredColimit.isColimitOf' _ _ ?_ ?_
  · intro y
    obtain ⟨i, a, ha⟩ := RationalTelescope.exists_inclusion (rationalCoefficientGroup X d)
      (Multiplicative.toAdd y)
    exact ⟨AsSmall.up.obj i, Additive.toMul a, congrArg Multiplicative.ofAdd ha.symm⟩
  · intro i a b h
    change homotopyGroup (cotensor CirclePower.space.{u} X) d at a b
    change RationalTelescope.inclusion (rationalCoefficientGroup X d) (AsSmall.down.obj i)
        (Additive.ofMul a) =
      RationalTelescope.inclusion (rationalCoefficientGroup X d) (AsSmall.down.obj i)
        (Additive.ofMul b) at h
    obtain ⟨l, hil, hl⟩ := RationalTelescope.inclusion_eq_eventually
      (rationalCoefficientGroup X d) (AsSmall.down.obj i) _ _ h
    let f : i ⟶ AsSmall.up.obj l := ⟨homOfLE hil⟩
    refine ⟨AsSmall.up.obj l, f, ?_⟩
    change homotopyMap ((rationalDiagram X).map f) d a =
      homotopyMap ((rationalDiagram X).map f) d b
    rw [rationalDiagram_homotopyMap, rationalDiagram_homotopyMap]
    change RationalTelescope.scalarTransition (rationalCoefficientGroup X d)
        (AsSmall.down.obj i) l hil (Additive.ofMul a) =
      RationalTelescope.scalarTransition (rationalCoefficientGroup X d)
        (AsSmall.down.obj i) l hil (Additive.ofMul b) at hl
    rw [RationalTelescope.scalarTransition_ofMul,
      RationalTelescope.scalarTransition_ofMul] at hl
    exact congrArg Additive.toMul hl

end OmegaSpectrum

end

end SerrePositivity.KST.Spectra
