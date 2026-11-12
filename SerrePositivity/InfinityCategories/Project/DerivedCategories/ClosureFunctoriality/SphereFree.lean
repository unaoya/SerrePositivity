module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.FamilyImage
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaPresentedFreeExtension

/-!
概要：κ-small sphere-free 基底の実延長の互換を公開する。
方針：既存の自由 sphere・余積の標準実同型を同じラベル写像で使う。
規約：小模型の perfect 代表は含めず、基底非依存の閉包入口へ渡せる形にする。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality
open CategoryTheory Limits DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (F : DGFunctor R C D)

/-- sphere-free 基底の同じ ordinal と次数を保持した実 dg 同型。 -/
def dgKappaSphereFreeExtensionIso {κ : Cardinal.{u}} (i : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaSphereFreeIndex C κ) :
    (dgModuleExtension R C D F).onClosed.obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaSphereFreeModule R C i) ≅
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaSphereFreeModule R D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaSphereFreeLabelMap R F i) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedFreeExtensionIso R C D F κ ⟨i⟩

/-- 任意の小さい直和添字で、自由 sphere の像と直和を同時に比較する。 -/
def dgModuleExtensionSphereCoproductIso {J : Type u} (x : J → C) (n : J → ℤ) :
    (dgModuleExtension R C D F).onClosed.obj (∐ (fun j => freeSphere R C (x j) (n j))) ≅
      ∐ (fun j => freeSphere R D (F.obj (x j)) (n j)) := by
  let : PreservesColimitsOfSize.{u, u} (dgModuleExtension R C D F).onClosed :=
    (dgModuleExtensionRestrictionAdjunction R C D F).leftAdjoint_preservesColimits
  exact PreservesCoproduct.iso (dgModuleExtension R C D F).onClosed _ ≪≫
    Sigma.mapIso (fun j => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleExtensionFreeSphereIso R C D F (x j) (n j))

end SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality
