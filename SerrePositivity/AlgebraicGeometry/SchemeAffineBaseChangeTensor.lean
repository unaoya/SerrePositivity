module

public import SerrePositivity.AlgebraicGeometry.SchemeAffinePullbackSections
public import SerrePositivity.AlgebraicGeometry.SchemeScalarMorphism
public import Mathlib.Algebra.Category.CommAlgCat.Basic

/-!
概要：Spec 上の実際の底変換のアフィン切断を、元の基底環上のテンソル積と比較する。
方針：Γ(Spec R) との二つの自然同型で pushout を移し、テンソル積の pushout と比較する。
規約：Γ(Spec R) = R を定義的等式として扱わず、canonical な写像を追う。
使われ方：平坦底変換と非平坦な閉厚化の両方での、実際の Čech 係数の比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
universe u
variable {R : Type u} [CommRing R] {X : Scheme.{u}}

/-- 構造射を指定したアフィン開の切断を、基底環上の代数として束ねる。 -/
def schemeAffineSectionAlgebra (iX : X ⟶ Spec (CommRingCat.of R)) (U : X.Opens) :
    CommAlgCat.{u} R := by
  letI : Algebra R Γ(X, U) :=
    (((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ iX.appLE ⊤ U (by simp)).hom).toAlgebra
  exact CommAlgCat.of R Γ(X, U)

variable {A : Type u} [CommRing A] [Algebra R A] {Y : Scheme.{u}}
variable (iX : X ⟶ Spec (CommRingCat.of R)) (iY : Y ⟶ Spec (CommRingCat.of A)) (g : Y ⟶ X)
variable (H : IsPullback g iY iX (Spec.map (CommRingCat.ofHom (algebraMap R A))))
variable (U : X.Opens) (hU : IsAffineOpen U)

include H hU in
/-- 実際のアフィン切断の正方形を、元の R と A を頂点に持つ pushout に移す。 -/
theorem schemeAffineBaseChangeSections_isPushout :
    IsPushout (CommRingCat.ofHom (algebraMap R (schemeAffineSectionAlgebra iX U)))
      (CommRingCat.ofHom (algebraMap R A))
      (g.appLE U (g ⁻¹ᵁ U) le_rfl)
      ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ iY.appLE ⊤ (g ⁻¹ᵁ U) (by simp)) := by
  have hY : g ⁻¹ᵁ U = g ⁻¹ᵁ U ⊓ iY ⁻¹ᵁ ⊤ := by simp
  haveI : IsIso (pushoutSection H (show (⊤ : (Spec (CommRingCat.of A)).Opens) ≤
      (Spec.map (CommRingCat.ofHom (algebraMap R A))) ⁻¹ᵁ ⊤ from le_rfl)
      (show U ≤ iX ⁻¹ᵁ ⊤ from le_top) hY) :=
    isIso_pushoutSection_of_isAffineOpen H _ _ _
      (isAffineOpen_top _) (isAffineOpen_top _) hU
  have hP := (isIso_pushoutSection_iff H (show (⊤ : (Spec (CommRingCat.of A)).Opens) ≤
      (Spec.map (CommRingCat.ofHom (algebraMap R A))) ⁻¹ᵁ ⊤ from le_rfl)
      (show U ≤ iX ⁻¹ᵁ ⊤ from le_top) hY).mp inferInstance
  refine hP.of_iso (Scheme.ΓSpecIso (CommRingCat.of R)) (Iso.refl _)
    (Scheme.ΓSpecIso (CommRingCat.of A)) (Iso.refl _) ?_ ?_ ?_ ?_
  · change iX.appLE ⊤ U _ ≫ 𝟙 _ =
      (Scheme.ΓSpecIso (CommRingCat.of R)).hom ≫
        (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ iX.appLE ⊤ U _
    simp only [Category.comp_id, Iso.hom_inv_id_assoc]
  · change (Spec.map (CommRingCat.ofHom (algebraMap R A))).appLE ⊤
        ((Spec.map (CommRingCat.ofHom (algebraMap R A))) ⁻¹ᵁ ⊤) le_rfl ≫
        (Scheme.ΓSpecIso (CommRingCat.of A)).hom = _
    rw [Scheme.Hom.appLE_eq_app]
    exact Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap R A))
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
  · simp only [Iso.refl_hom, Category.comp_id, Iso.hom_inv_id_assoc]

/-- 実際の底変換のアフィン切断と、元の環上のテンソル積の環同型。
平坦性を要求しないので、閉厚化にも同じ同型を使う。 -/
def schemeAffineBaseChangeTensorIso :
    CommRingCat.of (A ⊗[R] (schemeAffineSectionAlgebra iX U)) ≅ Γ(Y, g ⁻¹ᵁ U) :=
  (CommRingCat.isPushout_tensorProduct R A (schemeAffineSectionAlgebra iX U)).isoIsPushout
    (CommRingCat.of A) (CommRingCat.of (schemeAffineSectionAlgebra iX U))
    (schemeAffineBaseChangeSections_isPushout iX iY g H U hU).flip

/-- テンソル積の左の写像は、底変換先の構造射が誘導する scalar の写像。 -/
theorem schemeAffineBaseChangeTensorIso_left :
    CommRingCat.ofHom (S := A ⊗[R] (schemeAffineSectionAlgebra iX U))
        Algebra.TensorProduct.includeLeftRingHom ≫
        (schemeAffineBaseChangeTensorIso iX iY g H U hU).hom =
      (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ iY.appLE ⊤ (g ⁻¹ᵁ U) (by simp) := by
  exact IsPushout.inl_isoIsPushout_hom _ _ _ _

/-- テンソル積の右の写像は、元の構造層の実際の引き戻し。 -/
theorem schemeAffineBaseChangeTensorIso_right :
    CommRingCat.ofHom (S := A ⊗[R] (schemeAffineSectionAlgebra iX U))
        Algebra.TensorProduct.includeRight.toRingHom ≫
        (schemeAffineBaseChangeTensorIso iX iY g H U hU).hom =
      g.appLE U (g ⁻¹ᵁ U) le_rfl := by
  exact IsPushout.inr_isoIsPushout_hom _ _ _ _

end SerrePositivity.AlgebraicGeometry
