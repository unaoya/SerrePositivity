module
public import SerrePositivity.InfinityCategories.Derived.DGKernelCellModelLift
public import SerrePositivity.InfinityCategories.Derived.FunctorObjectIsoTransport
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet DifferentialGraded DGNerve MonoidalClosed
variable (R : Type u) [CommRing R] (D E : Type v)
  [DGCategory R D] [Small.{u} D] [DGCategory R E] [Small.{u} E]
local notation "DC" => DGCategoryCellResolution.Source R D
local notation "EC" => DGCategoryCellResolution.Source R E
local notation "FD" => DGCategoryCellResolution.augmentation R D
local notation "FE" => DGCategoryCellResolution.augmentation R E
def dgKernelCellRestrictionFunctor : BimoduleCategory R E D ⥤ BimoduleCategory R EC DC :=
  BimoduleCategory.middleLeftRestrictionFunctor R E D DC FD ⋙
    BimoduleCategory.middleRightRestrictionFunctor R E EC DC FE
def dgKernelCellLiftFamilyModelHomObject
    {C : Type w} [Category.{z} C] (Q : C ⥤ BimoduleCategory R EC DC) (X : C) :
    hoFunctor.obj ((ihom (dgModuleDerivedInfinityCategory R D)).obj
      (dgModuleDerivedInfinityCategory R E)) :=
  HomotopyCategory.mk (functorVertex ((dgCellModuleSourceEquivalence R D).inv ≫
    dgKernelDerivedInfinity R DC EC (BimoduleCategory.underlying R EC DC (Q.obj X)) ≫
      (dgCellModuleSourceEquivalence R E).hom))
def dgKernelCellLiftFamilyModelHomFunctor
    {C : Type w} [Category.{z} C]
    (P : C ⥤ BimoduleCategory R E D) (Q : C ⥤ BimoduleCategory R EC DC)
    (q : Q ⟶ P ⋙ dgKernelCellRestrictionFunctor R D E)
    (hQ : ∀ X, Bimodule.rightRelativeKFlat R EC DC
      (BimoduleCategory.underlying R EC DC (Q.obj X)))
    (hq : ∀ X, BimoduleCategory.quasiIso R EC DC (q.app X)) :
    C ⥤ hoFunctor.obj ((ihom (dgModuleDerivedInfinityCategory R D)).obj
      (dgModuleDerivedInfinityCategory R E)) :=
  functorOfObjectIsomorphisms (P ⋙ dgKernelDerivedFunctorHomFunctor R D E)
    (dgKernelCellLiftFamilyModelHomObject R D E Q)
    (fun X => dgKernelDerivedInfinity_cellModelLiftIso R D E
      (P.obj X) (Q.obj X) (q.app X) (hQ X) (hq X))
def dgKernelCellLiftFamilyHomIso
    {C : Type w} [Category.{z} C]
    (P : C ⥤ BimoduleCategory R E D) (Q : C ⥤ BimoduleCategory R EC DC)
    (q : Q ⟶ P ⋙ dgKernelCellRestrictionFunctor R D E)
    (hQ : ∀ X, Bimodule.rightRelativeKFlat R EC DC
      (BimoduleCategory.underlying R EC DC (Q.obj X)))
    (hq : ∀ X, BimoduleCategory.quasiIso R EC DC (q.app X)) :
    P ⋙ dgKernelDerivedFunctorHomFunctor R D E ≅
      dgKernelCellLiftFamilyModelHomFunctor R D E P Q q hQ hq :=
  functorOfObjectIsomorphismsIso (P ⋙ dgKernelDerivedFunctorHomFunctor R D E)
    (dgKernelCellLiftFamilyModelHomObject R D E Q)
    (fun X => dgKernelDerivedInfinity_cellModelLiftIso R D E
      (P.obj X) (Q.obj X) (q.app X) (hQ X) (hq X))
lemma dgKernelCellLiftFamilyHomIso_app
    {C : Type w} [Category.{z} C]
    (P : C ⥤ BimoduleCategory R E D) (Q : C ⥤ BimoduleCategory R EC DC)
    (q : Q ⟶ P ⋙ dgKernelCellRestrictionFunctor R D E)
    (hQ : ∀ X, Bimodule.rightRelativeKFlat R EC DC
      (BimoduleCategory.underlying R EC DC (Q.obj X)))
    (hq : ∀ X, BimoduleCategory.quasiIso R EC DC (q.app X)) (X : C) :
    (dgKernelCellLiftFamilyHomIso R D E P Q q hQ hq).app X =
      dgKernelDerivedInfinity_cellModelLiftIso R D E
        (P.obj X) (Q.obj X) (q.app X) (hQ X) (hq X) := rfl
lemma dgKernelCellLiftFamilyModelHomFunctor_map_raw
    {C : Type w} [Category.{z} C]
    (P : C ⥤ BimoduleCategory R E D) (Q : C ⥤ BimoduleCategory R EC DC)
    (q : Q ⟶ P ⋙ dgKernelCellRestrictionFunctor R D E)
    (hQ : ∀ X, Bimodule.rightRelativeKFlat R EC DC
      (BimoduleCategory.underlying R EC DC (Q.obj X)))
    (hq : ∀ X, BimoduleCategory.quasiIso R EC DC (q.app X))
    {X Y : C} (f : X ⟶ Y) :
    (dgKernelCellLiftFamilyModelHomFunctor R D E P Q q hQ hq).map f =
      functorHomPrecomp
        (dgKernelDerivedInfinity R DC EC (BimoduleCategory.underlying R EC DC (Q.obj X)) ≫
          (dgCellModuleSourceEquivalence R E).hom)
        (dgKernelDerivedInfinity R DC EC (BimoduleCategory.underlying R EC DC (Q.obj Y)) ≫
          (dgCellModuleSourceEquivalence R E).hom)
        (dgCellModuleSourceEquivalence R D).inv
        (functorHomPostcomp
          (dgKernelDerivedInfinity R DC EC (BimoduleCategory.underlying R EC DC (Q.obj X)))
          (dgKernelDerivedInfinity R DC EC (BimoduleCategory.underlying R EC DC (Q.obj Y)))
          (dgCellModuleSourceEquivalence R E).hom
          ((dgKernelDerivedFunctorHomFunctor R DC EC).map (Q.map f))) := by
  exact functorOfObjectIsomorphisms_map_eq_of_square
    (P ⋙ dgKernelDerivedFunctorHomFunctor R D E)
    (dgKernelCellLiftFamilyModelHomObject R D E Q)
    (fun X => dgKernelDerivedInfinity_cellModelLiftIso R D E
      (P.obj X) (Q.obj X) (q.app X) (hQ X) (hq X)) f _
    (dgKernelDerivedInfinity_cellModelLiftIso_hom_naturality R D E
      (q.app X) (q.app Y) (P.map f) (Q.map f) (q.naturality f)
      (hQ X) (hQ Y) (hq X) (hq Y))
end SerrePositivity.InfinityCategories
