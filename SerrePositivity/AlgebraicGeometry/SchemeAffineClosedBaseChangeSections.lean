module

public import SerrePositivity.AlgebraicGeometry.SchemeAffineBaseChangeTensor
public import Mathlib.RingTheory.TensorProduct.Quotient

/-!
概要：実際の閉厚化のアフィン切断を、元の切断の拡大イデアルによる商と比較する。
方針：切断のテンソル積の同型と、商環のテンソル積の canonical な同型を合成する。
規約：平坦性を要求せず、射影は実際の構造層の引き戻しと一致する。
使われ方：Iⁿ による閉厚化と Rees の商の Čech 計算を同じ写像で照合する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {X Y : Scheme.{u}}
variable (iX : X ⟶ Spec (CommRingCat.of R))
variable (iY : Y ⟶ Spec (CommRingCat.of (R ⧸ I))) (g : Y ⟶ X)
variable (H : IsPullback g iY iX (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))
variable (U : X.Opens) (hU : IsAffineOpen U)

/-- 実際の閉厚化のアフィン切断は、元の切断の拡大イデアルによる商。 -/
def schemeAffineClosedBaseChangeSectionIso :
    CommRingCat.of ((schemeAffineSectionAlgebra iX U) ⧸
      I.map (algebraMap R (schemeAffineSectionAlgebra iX U))) ≅ Γ(Y, g ⁻¹ᵁ U) :=
  (Algebra.TensorProduct.quotIdealMapEquivQuotTensor (schemeAffineSectionAlgebra iX U) I).toRingEquiv.toCommRingCatIso ≪≫
    schemeAffineBaseChangeTensorIso iX iY g H U hU

/-- 元の切断から商へ射影する写像は、実際の閉厚化への引き戻し。 -/
theorem schemeAffineClosedBaseChangeSectionIso_projection :
    CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap R (schemeAffineSectionAlgebra iX U)))) ≫
      (schemeAffineClosedBaseChangeSectionIso I iX iY g H U hU).hom =
        g.appLE U (g ⁻¹ᵁ U) le_rfl := by
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro b
  change (schemeAffineBaseChangeTensorIso iX iY g H U hU).hom.hom
    ((1 : R ⧸ I) ⊗ₜ[R] (b : schemeAffineSectionAlgebra iX U)) = _
  exact congrArg (fun f : CommRingCat.of (schemeAffineSectionAlgebra iX U) ⟶
    Γ(Y, g ⁻¹ᵁ U) ↦ f.hom b) (schemeAffineBaseChangeTensorIso_right iX iY g H U hU)

include H hU in
/-- 実際の閉厚化のアフィン切断への引き戻しは全射。 -/
theorem schemeAffineClosedBaseChangeSections_surjective :
    Function.Surjective (g.appLE U (g ⁻¹ᵁ U) le_rfl).hom := by
  let e := schemeAffineClosedBaseChangeSectionIso I iX iY g H U hU
  have hs := e.commRingCatIsoToRingEquiv.surjective.comp
    (Ideal.Quotient.mk_surjective (I := I.map (algebraMap R (schemeAffineSectionAlgebra iX U))))
  have he := congrArg (fun f : CommRingCat.of (schemeAffineSectionAlgebra iX U) ⟶
      Γ(Y, g ⁻¹ᵁ U) ↦ fun b ↦ f.hom b)
    (schemeAffineClosedBaseChangeSectionIso_projection I iX iY g H U hU)
  intro y
  obtain ⟨b, hb⟩ := hs y
  exact ⟨b, (congrFun he b).symm.trans hb⟩

include H hU in
/-- 実際の閉厚化へのアフィン切断の射の核は、元の切断での拡大イデアル。 -/
theorem schemeAffineClosedBaseChangeSections_ker :
    RingHom.ker (g.appLE U (g ⁻¹ᵁ U) le_rfl).hom =
      I.map (algebraMap R (schemeAffineSectionAlgebra iX U)) := by
  let e := schemeAffineClosedBaseChangeSectionIso I iX iY g H U hU
  ext b
  change (g.appLE U (g ⁻¹ᵁ U) le_rfl).hom b = 0 ↔ _
  have he := congrArg (fun f : CommRingCat.of (schemeAffineSectionAlgebra iX U) ⟶
      Γ(Y, g ⁻¹ᵁ U) ↦ f.hom b)
    (schemeAffineClosedBaseChangeSectionIso_projection I iX iY g H U hU)
  constructor
  · intro hb
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    apply e.commRingCatIsoToRingEquiv.injective
    exact (he.trans hb).trans (map_zero e.hom.hom).symm
  · intro hb
    have hz := Ideal.Quotient.eq_zero_iff_mem.mpr hb
    exact he.symm.trans ((congrArg e.hom.hom hz).trans (map_zero e.hom.hom))

end SerrePositivity.AlgebraicGeometry
