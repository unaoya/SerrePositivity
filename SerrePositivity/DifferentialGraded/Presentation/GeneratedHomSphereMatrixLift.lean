module
public import SerrePositivity.DifferentialGraded.Presentation.GeneratedHomSphereExtensionComparison
public import SerrePositivity.DifferentialGraded.Functor.CoproductMatrixComparison
public import Mathlib.CategoryTheory.Adjunction.Limits
/-!
概要：コードの全シフト自由閉射行列を、実延長と直和端点の同型付きで元の行列へ比較する。
方針：support 内の係数を持ち上げ、各成分の可換式を余積と有限和で束ねる。
規約：元の閉射行列全体の等式を証明し、support 外の係数は零とする。
使われ方：c′ の自由 seed 間閉射の共通源精密化。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits
variable {I : Type u} (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  (κ : Cardinal.{u}) (a : κ.ord.ToType) (source target : I → Set.Iio a) (degree : I → ℤ)
  (value : Set.Iio a → D)
  (coefficient : ∀ i, GradedHom R (value (source i)) (value (target i)) (degree i))
  (hκ : Cardinal.aleph0 ≤ κ) (hI : Cardinal.mk I ≤ κ)
namespace DGGeneratedHomWord
local notation "C" => (DGCategoryPresentationCode.Objects R κ
  (code R D κ a source target degree value coefficient hκ hI))
local notation "L" => codeEvaluation R D κ a source target degree value coefficient hκ hI

structure SphereMatrixData (J K : Type u) where
  x : J → C
  y : K → C
  n : J → ℤ
  m : K → ℤ
  support : J → Finset K
  arrow : ∀ i j, freeSphere R D (value (x i)) (n i) ⟶ freeSphere R D (value (y j)) (m j)
  contained : ∀ i j, j ∈ support i →
    freeSphereClosedCoefficient R D (value (x i)) (value (y j)) (n i) (m j) (arrow i j) ∈
      linearSpan source target degree R D value coefficient (x i) (y j) (n i - m j)

variable {J K : Type u}
local notation "Data" => SphereMatrixData R D κ a source target degree value coefficient hκ hI J K

def codeSphereMatrixEntry (p : Data) (i : J) (j : K) :
    freeSphere R C (p.x i) (p.n i) ⟶ freeSphere R C (p.y j) (p.m j) := by
  classical
  exact if h : j ∈ p.support i then
    codeFreeSphereClosedArrow R D κ a source target degree value coefficient hκ hI
      (p.x i) (p.y j) (p.n i) (p.m j) (p.arrow i j) (p.contained i j h)
    else 0

def codeSphereMatrixLift (p : Data) :
    (∐ fun i => freeSphere R C (p.x i) (p.n i)) ⟶ ∐ fun j => freeSphere R C (p.y j) (p.m j) :=
  Sigma.desc (fun i => ∑ j ∈ p.support i,
    codeSphereMatrixEntry R D κ a source target degree value coefficient hκ hI p i j ≫
      Sigma.ι (fun j => freeSphere R C (p.y j) (p.m j)) j)

set_option maxRecDepth 1024 in
lemma codeSphereMatrixLift_extension_comm (p : Data) :
    let F := (dgModuleExtension R C D L).onClosed
    letI : PreservesColimitsOfSize.{u, u} F :=
      (dgModuleExtensionRestrictionAdjunction R C D L).leftAdjoint_preservesColimits
    F.map (codeSphereMatrixLift R D κ a source target degree value coefficient hκ hI p) ≫
      (coproductFamilyImageIso F (fun j => freeSphere R C (p.y j) (p.m j))
        (fun j => freeSphere R D (value (p.y j)) (p.m j))
        (fun j => dgModuleExtensionFreeAtIso R C D L (p.y j) (complexSphere R (p.m j)))).hom =
    (coproductFamilyImageIso F (fun i => freeSphere R C (p.x i) (p.n i))
      (fun i => freeSphere R D (value (p.x i)) (p.n i))
      (fun i => dgModuleExtensionFreeAtIso R C D L (p.x i) (complexSphere R (p.n i)))).hom ≫
    Sigma.desc (fun i => ∑ j ∈ p.support i, p.arrow i j ≫
      Sigma.ι (fun j => freeSphere R D (value (p.y j)) (p.m j)) j) := by
  classical
  dsimp only
  letI : PreservesColimitsOfSize.{u, u} (dgModuleExtension R C D L).onClosed :=
    (dgModuleExtensionRestrictionAdjunction R C D L).leftAdjoint_preservesColimits
  apply coproductFamilyImageIso_matrix
  intro i j hj
  simp only [codeSphereMatrixEntry, dif_pos hj]
  exact codeFreeSphereClosedArrow_extension_comm R D κ a source target degree value coefficient
    hκ hI (p.x i) (p.y j) (p.n i) (p.m j) (p.arrow i j) (p.contained i j hj)

end DGGeneratedHomWord
end SerrePositivity.DifferentialGraded
