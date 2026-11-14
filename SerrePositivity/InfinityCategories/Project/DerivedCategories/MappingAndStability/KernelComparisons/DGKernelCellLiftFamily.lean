module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.KernelComparisons.DGKernelCellModelLift
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.SimplicialFunctors.FunctorObjectIsoTransport
/-!
概要：一般の許容 cell 模型の族と augmentation の圏で実模型作用と比較をまとめる。
方針：対象を明示した h Fun 値関手を同じ比較で移し、全射を元の実前後合成へ同定する。
規約：原 kernel の平坦性を追加しない。使われ方：単位・合成・模型変更の整合性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet DifferentialGraded MonoidalClosed
variable (R : Type u) [CommRing R] (D E : Type v)
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
local notation "DC" => _root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.Source R D
local notation "EC" => _root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.Source R E
local notation "FD" => _root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.augmentation R D
local notation "FE" => _root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.augmentation R E
def dgKernelCellRestrictionFunctor : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R E D ⥤ BimoduleCategory R EC DC :=
  _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.middleLeftRestrictionFunctor R E D DC FD ⋙
    _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.middleRightRestrictionFunctor R E EC DC FE
def dgKernelCellLiftFamilyModelHomObject
    {C : Type w} [Category.{z} C] (Q : C ⥤ _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R EC DC) (X : C) :
    hoFunctor.obj ((ihom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R D)).obj
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R E)) :=
  HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellModuleSourceEquivalence R D).inv ≫
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R DC EC (BimoduleCategory.underlying R EC DC (Q.obj X)) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellModuleSourceEquivalence R E).hom))
def dgKernelCellLiftFamilyModelHomFunctor
    {C : Type w} [Category.{z} C]
    (P : C ⥤ _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R E D) (Q : C ⥤ _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R EC DC)
    (q : Q ⟶ P ⋙ dgKernelCellRestrictionFunctor R D E)
    (hQ : ∀ X, _root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat R EC DC
      (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R EC DC (Q.obj X)))
    (hq : ∀ X, _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.quasiIso R EC DC (q.app X)) :
    C ⥤ hoFunctor.obj ((ihom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R D)).obj
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R E)) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorOfObjectIsomorphisms (P ⋙ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedFunctorHomFunctor R D E)
    (dgKernelCellLiftFamilyModelHomObject R D E Q)
    (fun X => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_cellModelLiftIso R D E
      (P.obj X) (Q.obj X) (q.app X) (hQ X) (hq X))
def dgKernelCellLiftFamilyHomIso
    {C : Type w} [Category.{z} C]
    (P : C ⥤ _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R E D) (Q : C ⥤ _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R EC DC)
    (q : Q ⟶ P ⋙ dgKernelCellRestrictionFunctor R D E)
    (hQ : ∀ X, _root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat R EC DC
      (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R EC DC (Q.obj X)))
    (hq : ∀ X, _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.quasiIso R EC DC (q.app X)) :
    P ⋙ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedFunctorHomFunctor R D E ≅
      dgKernelCellLiftFamilyModelHomFunctor R D E P Q q hQ hq :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorOfObjectIsomorphismsIso (P ⋙ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedFunctorHomFunctor R D E)
    (dgKernelCellLiftFamilyModelHomObject R D E Q)
    (fun X => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_cellModelLiftIso R D E
      (P.obj X) (Q.obj X) (q.app X) (hQ X) (hq X))
lemma dgKernelCellLiftFamilyHomIso_app
    {C : Type w} [Category.{z} C]
    (P : C ⥤ _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R E D) (Q : C ⥤ _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R EC DC)
    (q : Q ⟶ P ⋙ dgKernelCellRestrictionFunctor R D E)
    (hQ : ∀ X, _root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat R EC DC
      (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R EC DC (Q.obj X)))
    (hq : ∀ X, _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.quasiIso R EC DC (q.app X)) (X : C) :
    (dgKernelCellLiftFamilyHomIso R D E P Q q hQ hq).app X =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_cellModelLiftIso R D E
        (P.obj X) (Q.obj X) (q.app X) (hQ X) (hq X) := rfl
lemma dgKernelCellLiftFamilyModelHomFunctor_map_raw
    {C : Type w} [Category.{z} C]
    (P : C ⥤ _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R E D) (Q : C ⥤ _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R EC DC)
    (q : Q ⟶ P ⋙ dgKernelCellRestrictionFunctor R D E)
    (hQ : ∀ X, _root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat R EC DC
      (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R EC DC (Q.obj X)))
    (hq : ∀ X, _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.quasiIso R EC DC (q.app X))
    {X Y : C} (f : X ⟶ Y) :
    (dgKernelCellLiftFamilyModelHomFunctor R D E P Q q hQ hq).map f =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R DC EC (BimoduleCategory.underlying R EC DC (Q.obj X)) ≫
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellModuleSourceEquivalence R E).hom)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R DC EC (BimoduleCategory.underlying R EC DC (Q.obj Y)) ≫
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellModuleSourceEquivalence R E).hom)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellModuleSourceEquivalence R D).inv
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R DC EC (BimoduleCategory.underlying R EC DC (Q.obj X)))
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R DC EC (BimoduleCategory.underlying R EC DC (Q.obj Y)))
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellModuleSourceEquivalence R E).hom
          ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedFunctorHomFunctor R DC EC).map (Q.map f))) := by
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorOfObjectIsomorphisms_map_eq_of_square
    (P ⋙ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedFunctorHomFunctor R D E)
    (dgKernelCellLiftFamilyModelHomObject R D E Q)
    (fun X => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_cellModelLiftIso R D E
      (P.obj X) (Q.obj X) (q.app X) (hQ X) (hq X)) f _
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_cellModelLiftIso_hom_naturality R D E
      (q.app X) (q.app Y) (P.map f) (Q.map f) (q.naturality f)
      (hQ X) (hQ Y) (hq X) (hq Y))
end SerrePositivity.InfinityCategories.Project.DerivedCategories
