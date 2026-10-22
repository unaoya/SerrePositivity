module
public import SerrePositivity.InfinityCategories.Derived.DGKernelCellModelNaturality
public import SerrePositivity.InfinityCategories.Derived.FunctorObjectIsoTransport
/-!
概要：指定済みの cell 比較を保って h Fun 値の作用と一般の cell 模型比較を構成する。
方針：同じ比較の共役による関手性と、augmentation の可換四角形の自然性を使う。
規約：原 kernel の平坦性は不要。使われ方：一般 cell 模型の単位・合成・比較の整合性。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory
open SSet DifferentialGraded DGNerve MonoidalClosed
variable (R : Type u) [CommRing R] (D E : Type v)
  [DGCategory R D] [Small.{u} D] [DGCategory R E] [Small.{u} E]
local notation "DC" => DGCategoryCellResolution.Source R D
local notation "EC" => DGCategoryCellResolution.Source R E
def dgKernelCellModelFunctorHomObject (P : BimoduleCategory R E D) :
    hoFunctor.obj ((ihom (dgModuleDerivedInfinityCategory R D)).obj
      (dgModuleDerivedInfinityCategory R E)) :=
  HomotopyCategory.mk (functorVertex ((dgCellModuleSourceEquivalence R D).inv ≫
    dgKernelDerivedInfinity R DC EC
      (BimoduleCategory.underlying R EC DC
        (dgKernelCellModel R D E (BimoduleCategory.underlying R E D P))) ≫
      (dgCellModuleSourceEquivalence R E).hom))
def dgKernelCellModelFunctorHomFunctor : BimoduleCategory R E D ⥤
    hoFunctor.obj ((ihom (dgModuleDerivedInfinityCategory R D)).obj
      (dgModuleDerivedInfinityCategory R E)) :=
  functorOfObjectIsomorphisms (dgKernelDerivedFunctorHomFunctor R D E)
    (dgKernelCellModelFunctorHomObject R D E)
    (fun P => dgKernelDerivedInfinity_cellModelIso R D E
      (BimoduleCategory.underlying R E D P))
def dgKernelCellModelFunctorHomIso :
    dgKernelDerivedFunctorHomFunctor R D E ≅ dgKernelCellModelFunctorHomFunctor R D E :=
  functorOfObjectIsomorphismsIso (dgKernelDerivedFunctorHomFunctor R D E)
    (dgKernelCellModelFunctorHomObject R D E)
    (fun P => dgKernelDerivedInfinity_cellModelIso R D E
      (BimoduleCategory.underlying R E D P))
lemma dgKernelCellModelFunctorHomIso_app (P : BimoduleCategory R E D) :
    (dgKernelCellModelFunctorHomIso R D E).app P =
      dgKernelDerivedInfinity_cellModelIso R D E
        (BimoduleCategory.underlying R E D P) := rfl
variable {P0 P1 : BimoduleCategory R E D}
local notation "p0" => BimoduleCategory.underlying R E D P0
local notation "p1" => BimoduleCategory.underlying R E D P1
local notation "FD" => DGCategoryCellResolution.augmentation R D
local notation "FE" => DGCategoryCellResolution.augmentation R E
local notation "Q0" => dgKernelCellModel R D E p0
local notation "Q1" => dgKernelCellModel R D E p1
local notation "T0" => dgKernelCellResolution R D E p0
local notation "T1" => dgKernelCellResolution R D E p1
local notation "L" => BimoduleCategory.middleLeftRestrictionFunctor R E D DC FD
local notation "S" => BimoduleCategory.middleRightRestrictionFunctor R E EC DC FE
lemma dgKernelCellModelFunctorHomFunctor_map_raw
    (g : P0 ⟶ P1) (b : Q0 ⟶ Q1)
    (h : b ≫ (T1).π = (T0).π ≫ (S).map ((L).map g)) :
    (dgKernelCellModelFunctorHomFunctor R D E).map g =
      functorHomPrecomp
        (dgKernelDerivedInfinity R DC EC (BimoduleCategory.underlying R EC DC Q0) ≫
          (dgCellModuleSourceEquivalence R E).hom)
        (dgKernelDerivedInfinity R DC EC (BimoduleCategory.underlying R EC DC Q1) ≫
          (dgCellModuleSourceEquivalence R E).hom)
        (dgCellModuleSourceEquivalence R D).inv
        (functorHomPostcomp
          (dgKernelDerivedInfinity R DC EC (BimoduleCategory.underlying R EC DC Q0))
          (dgKernelDerivedInfinity R DC EC (BimoduleCategory.underlying R EC DC Q1))
          (dgCellModuleSourceEquivalence R E).hom
          ((dgKernelDerivedFunctorHomFunctor R DC EC).map b)) := by
  exact functorOfObjectIsomorphisms_map_eq_of_square (dgKernelDerivedFunctorHomFunctor R D E)
    (dgKernelCellModelFunctorHomObject R D E)
    (fun P => dgKernelDerivedInfinity_cellModelIso R D E
      (BimoduleCategory.underlying R E D P)) g _
    (dgKernelDerivedInfinity_cellModelIso_hom_naturality R D E g b h)
end SerrePositivity.InfinityCategories
