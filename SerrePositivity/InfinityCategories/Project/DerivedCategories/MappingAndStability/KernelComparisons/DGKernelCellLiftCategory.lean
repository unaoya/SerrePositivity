module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.KernelComparisons.DGKernelCellLiftFamily
public import Mathlib.CategoryTheory.Comma.Basic
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
/-!
概要：一般の許容 cell 模型の族と augmentation の圏で実模型作用と比較をまとめる。
方針：対象を明示した h Fun 値関手を同じ比較で移し、全射を元の実前後合成へ同定する。
規約：原 kernel の平坦性を追加しない。使われ方：単位・合成・模型変更の整合性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet DifferentialGraded MonoidalClosed
variable (R : Type u) [CommRing R] (D E : Type v)
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
local notation "DC" => _root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.Source R D
local notation "EC" => _root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.Source R E
local notation "FD" => _root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.augmentation R D
local notation "FE" => _root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.augmentation R E
abbrev DGKernelCellLiftComma :=
  Comma (𝟭 (BimoduleCategory R EC DC)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellRestrictionFunctor R D E)
def dgKernelCellLiftProperty : ObjectProperty (DGKernelCellLiftComma R D E) := fun X =>
  _root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat R EC DC (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R EC DC X.left) ∧
    _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.quasiIso R EC DC X.hom
abbrev DGKernelCellLiftCategory := (dgKernelCellLiftProperty R D E).FullSubcategory
def dgKernelCellLiftSourceFunctor : DGKernelCellLiftCategory R D E ⥤ BimoduleCategory R E D :=
  (dgKernelCellLiftProperty R D E).ι ⋙
    Comma.snd (𝟭 (BimoduleCategory R EC DC)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellRestrictionFunctor R D E)
def dgKernelCellLiftModelFunctor : DGKernelCellLiftCategory R D E ⥤
    BimoduleCategory R EC DC :=
  (dgKernelCellLiftProperty R D E).ι ⋙
    Comma.fst (𝟭 (BimoduleCategory R EC DC)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellRestrictionFunctor R D E)
def dgKernelCellLiftOriginalHomFunctor : DGKernelCellLiftCategory R D E ⥤
    hoFunctor.obj ((ihom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R D)).obj
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R E)) :=
  dgKernelCellLiftSourceFunctor R D E ⋙ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedFunctorHomFunctor R D E
def dgKernelCellLiftAugmentation : dgKernelCellLiftModelFunctor R D E ⟶
    dgKernelCellLiftSourceFunctor R D E ⋙ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellRestrictionFunctor R D E where
  app X := X.obj.hom
  naturality _ _ f := f.hom.w
def dgKernelCellLiftModelHomFunctor : DGKernelCellLiftCategory R D E ⥤
    hoFunctor.obj ((ihom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R D)).obj
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R E)) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellLiftFamilyModelHomFunctor R D E (dgKernelCellLiftSourceFunctor R D E)
    (dgKernelCellLiftModelFunctor R D E) (dgKernelCellLiftAugmentation R D E)
    (fun X => X.property.1) (fun X => X.property.2)
def dgKernelCellLiftHomIso :
    dgKernelCellLiftOriginalHomFunctor R D E ≅ dgKernelCellLiftModelHomFunctor R D E :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellLiftFamilyHomIso R D E (dgKernelCellLiftSourceFunctor R D E)
    (dgKernelCellLiftModelFunctor R D E) (dgKernelCellLiftAugmentation R D E)
    (fun X => X.property.1) (fun X => X.property.2)
lemma dgKernelCellLiftHomIso_app (X : DGKernelCellLiftCategory R D E) :
    (dgKernelCellLiftHomIso R D E).app X =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_cellModelLiftIso R D E
        X.obj.right X.obj.left X.obj.hom X.property.1 X.property.2 := rfl
lemma dgKernelCellLiftModelHomFunctor_map_raw
    {X Y : DGKernelCellLiftCategory R D E} (f : X ⟶ Y) :
    (dgKernelCellLiftModelHomFunctor R D E).map f =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R DC EC (BimoduleCategory.underlying R EC DC X.obj.left) ≫
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellModuleSourceEquivalence R E).hom)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R DC EC (BimoduleCategory.underlying R EC DC Y.obj.left) ≫
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellModuleSourceEquivalence R E).hom)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellModuleSourceEquivalence R D).inv
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R DC EC (BimoduleCategory.underlying R EC DC X.obj.left))
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R DC EC (BimoduleCategory.underlying R EC DC Y.obj.left))
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellModuleSourceEquivalence R E).hom
          ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedFunctorHomFunctor R DC EC).map f.hom.left)) := by
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellLiftFamilyModelHomFunctor_map_raw R D E
    (dgKernelCellLiftSourceFunctor R D E) (dgKernelCellLiftModelFunctor R D E)
    (dgKernelCellLiftAugmentation R D E) (fun X => X.property.1) (fun X => X.property.2) f
end SerrePositivity.InfinityCategories.Project.DerivedCategories
