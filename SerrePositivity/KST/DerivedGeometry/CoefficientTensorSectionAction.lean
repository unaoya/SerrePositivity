module

public import SerrePositivity.KST.DerivedGeometry.CoefficientActionSections

/-!
概要：構造層加群の H 作用と局所スカラー作用からテンソル係数環の作用を構成する。
方針：切断の線形自己準同型代数への二つの可換な射にテンソル積の普遍性を適用する。
規約：H は単位的結合環で、可換性・平坦性を仮定しない。
使われ方：KST D4・T1′、Toën §3.2 のアフィン係数層化。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct
namespace SerrePositivity.KST.DerivedGeometry
variable {A : Type u} [CommRing A] (H : Type u) [Ring H] [Algebra A H]
  {X : Scheme.{u}} (a : A →+* Γ(X, ⊤))

/--
概要：局所テンソル係数環から切断の線形自己準同型環への環準同型。
方針：H の作用と可換な局所スカラー作用にテンソル積の普遍性を使う。
規約：二つの作用の基礎環 A 上の一致は証明された層の射の等式で与える。
使われ方：KST D4・T1′、Toën §3.2 の係数加群層の構成。
-/
def coefficientTensorSectionEnd (M : X.Modules) (ρ : H →+* End M)
    (hρ : ∀ r : A, (ρ (algebraMap A H r)).asHom = structureScalarAction a M r)
    (U : X.Opens) :
    letI := sectionAlgebra a U
    letI := structureSectionModule M U
    H ⊗[A] Γ(X, U) →+* Module.End Γ(X, U) (M.val.obj (.op U)) := by
  letI := sectionAlgebra a U
  letI := structureSectionModule M U
  letI := structureSectionEndAlgebra a M U
  letI : IsScalarTower A Γ(X, U) (Module.End Γ(X, U) (M.val.obj (.op U))) :=
    IsScalarTower.of_algebraMap_smul fun r f => rfl
  let α := coefficientSectionAction a H M ρ hρ U
  let β := IsScalarTower.toAlgHom A Γ(X, U) (Module.End Γ(X, U) (M.val.obj (.op U)))
  exact (Algebra.TensorProduct.lift α β (by
    intro h r
    change α h * algebraMap Γ(X, U) _ r = algebraMap Γ(X, U) _ r * α h
    exact (Algebra.commutes r (α h)).symm)).toRingHom

/--
概要：テンソル係数の環準同型で切断に実際の左加群構造を与える。
方針：線形自己準同型環の標準作用を構成済みの環準同型へ沿って制限する。
規約：係数環は層化前のテンソル環。
使われ方：KST D4・T1′、Toën §3.2 のテンソル係数前層。
-/
@[instance_reducible]
def coefficientTensorSectionModule (M : X.Modules) (ρ : H →+* End M)
    (hρ : ∀ r : A, (ρ (algebraMap A H r)).asHom = structureScalarAction a M r)
    (U : X.Opens) :
    letI := sectionAlgebra a U
    Module (H ⊗[A] Γ(X, U)) (M.val.obj (.op U)) := by
  letI := sectionAlgebra a U
  letI := structureSectionModule M U
  exact Module.compHom _ (coefficientTensorSectionEnd H a M ρ hρ U)

/--
概要：純テンソルの作用は H の作用と局所スカラーの作用の合成。
方針：テンソル積の普遍性の評価公式と H の作用の O 線形性を使う。
規約：H の非可換性を保持したまま局所スカラーだけを移動する。
使われ方：KST D4・T1′、Toën §3.2 の制限写像の半線形性。
-/
theorem coefficientTensorSectionEnd_tmul_apply (M : X.Modules) (ρ : H →+* End M)
    (hρ : ∀ r : A, (ρ (algebraMap A H r)).asHom = structureScalarAction a M r)
    (U : X.Opens) (h : H) (r : Γ(X, U)) (m : M.val.obj (.op U)) :
    letI := sectionAlgebra a U
    letI := structureSectionModule M U
    (coefficientTensorSectionEnd H a M ρ hρ U (h ⊗ₜ[A] r)) m =
      r • ((ρ h).asHom.val.app (.op U)).hom m := by
  letI := sectionAlgebra a U
  letI := structureSectionModule M U
  change ((ρ h).asHom.val.app (.op U)).hom (r • m) = _
  exact ((ρ h).asHom.val.app (.op U)).hom.map_smul r m

end SerrePositivity.KST.DerivedGeometry
