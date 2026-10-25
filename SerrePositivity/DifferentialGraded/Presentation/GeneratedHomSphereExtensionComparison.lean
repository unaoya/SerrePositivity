module
public import SerrePositivity.DifferentialGraded.Presentation.GeneratedHomSphereArrowLift
public import SerrePositivity.DifferentialGraded.Module.FreeSphereImageCoefficient
/-!
概要：コード内に持ち上げた任意シフト自由閉射を、実延長の端点同型付きで元の閉射へ比較する。
方針：元の Hom 係数で自由閉射を検出し、自由延長の自然性へ接続する。
規約：元の閉射全体と同じ実端点同型を保持する。
使われ方：c′ の全シフト自由閉射族の共通源精密化。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable {I : Type u} (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  (κ : Cardinal.{u}) (a : κ.ord.ToType) (source target : I → Set.Iio a) (degree : I → ℤ)
  (value : Set.Iio a → D)
  (coefficient : ∀ i, GradedHom R (value (source i)) (value (target i)) (degree i))
  (hκ : Cardinal.aleph0 ≤ κ) (hI : Cardinal.mk I ≤ κ)
namespace DGGeneratedHomWord
local notation "C" => (DGCategoryPresentationCode.Objects R κ
  (code R D κ a source target degree value coefficient hκ hI))
local notation "L" => codeEvaluation R D κ a source target degree value coefficient hκ hI
lemma codeFreeSphereClosedArrow_image (x y : C) (n m : ℤ)
    (f : freeSphere R D (value x) n ⟶ freeSphere R D (value y) m)
    (hf : freeSphereClosedCoefficient R D (value x) (value y) n m f ∈
      linearSpan source target degree R D value coefficient x y (n - m)) :
    dgFreeClosedArrowImage R C D L x y (complexSphere R n) (complexSphere R m)
      (codeFreeSphereClosedArrow R D κ a source target degree value coefficient hκ hI x y n m f hf) = f := by
  apply freeSphereClosedCoefficient_injective R D (value x) (value y) n m
  exact (dgFreeClosedArrowImage_sphere_coefficient R C D L x y n m
    (codeFreeSphereClosedArrow R D κ a source target degree value coefficient hκ hI x y n m f hf)).trans
    (codeFreeSphereClosedArrow_coefficient_map R D κ a source target degree value coefficient
      hκ hI x y n m f hf)

lemma codeFreeSphereClosedArrow_extension_comm (x y : C) (n m : ℤ)
    (f : freeSphere R D (value x) n ⟶ freeSphere R D (value y) m)
    (hf : freeSphereClosedCoefficient R D (value x) (value y) n m f ∈
      linearSpan source target degree R D value coefficient x y (n - m)) :
    (dgModuleExtension R C D L).onClosed.map
      (codeFreeSphereClosedArrow R D κ a source target degree value coefficient hκ hI x y n m f hf) ≫
      (dgModuleExtensionFreeAtIso R C D L y (complexSphere R m)).hom =
    (dgModuleExtensionFreeAtIso R C D L x (complexSphere R n)).hom ≫ f := by
  have h := dgModuleExtensionFreeAtIso_arrow_comm R C D L x y
    (complexSphere R n) (complexSphere R m)
    (codeFreeSphereClosedArrow R D κ a source target degree value coefficient hκ hI x y n m f hf)
  rw [codeFreeSphereClosedArrow_image R D κ a source target degree value coefficient
    hκ hI x y n m f hf] at h
  exact h

end DGGeneratedHomWord
end SerrePositivity.DifferentialGraded
