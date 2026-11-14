module

public import SerrePositivity.AlgebraicGeometry.SchemeAffineSectionModule
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
概要：アフィン底変換の切断の同型を、実際の構造層の係数加群の間で述べる。
方針：構造射で束ねた切断の比較を両端で用いる。
規約：平坦性を仮定せず、元の環の写像からのスカラー拡大を使う。
使われ方：閉厚化と平坦底変換の実際の Čech 係数への接続。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct
universe u
variable {R A : Type u} [CommRing R] [CommRing A] (α : R →+* A)
variable {X Y : Scheme.{u}}
variable (iX : X ⟶ Spec (CommRingCat.of R)) (iY : Y ⟶ Spec (CommRingCat.of A))
variable (g : Y ⟶ X)
variable (H : IsPullback g iY iX (Spec.map (CommRingCat.ofHom α)))
variable (U : X.Opens) (hU : IsAffineOpen U)

/-- アフィン底変換の実際の切断の同型を、元の構造層の係数加群の間で述べる。 -/
def schemeAffineBaseChangeNativeSectionsEquiv :
    ((ModuleCat.extendScalars α).obj
      ((schemeStructureCechPresheaf X ⋙ ModuleCat.restrictScalars
        (schemeScalarHom X iX)).obj (op U))) ≃ₗ[A]
      ((schemeStructureCechPresheaf Y ⋙ ModuleCat.restrictScalars
        (schemeScalarHom Y iY)).obj (op (g ⁻¹ᵁ U))) := by
  letI : Algebra R A := α.toAlgebra
  exact (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl A A)
    (schemeAffineSectionModuleEquiv iX U)).trans
      ((schemeAffineBaseChangeSectionsLinearEquiv iX iY g H U hU).trans
        (schemeAffineSectionModuleEquiv iY (g ⁻¹ᵁ U)).symm)

/-- 実際の切断の同型は、1 と元の切断の純テンソルを構造層の引き戻しへ送る。 -/
theorem schemeAffineBaseChangeNativeSectionsEquiv_unit
    (x : (schemeStructureCechPresheaf X ⋙ ModuleCat.restrictScalars
      (schemeScalarHom X iX)).obj (op U)) :
    schemeAffineBaseChangeNativeSectionsEquiv α iX iY g H U hU
      ((ModuleCat.extendRestrictScalarsAdj α).unit.app
        ((schemeStructureCechPresheaf X ⋙ ModuleCat.restrictScalars
          (schemeScalarHom X iX)).obj (op U)) x) =
      (g.appLE U (g ⁻¹ᵁ U) le_rfl).hom x := by
  letI : Algebra R A := α.toAlgebra
  change (schemeAffineBaseChangeTensorIso iX iY g H U hU).hom.hom
    ((1 : A) ⊗ₜ[R] (x : schemeAffineSectionAlgebra iX U)) = _
  rw [schemeAffineBaseChangeTensorIso_tmul, map_one, one_mul]

end SerrePositivity.AlgebraicGeometry
