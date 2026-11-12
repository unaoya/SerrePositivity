module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKernelCellModelNaturality
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.FunctorObjectIsoTransport
/-!
概要：指定済みの cell 比較を保って h Fun 値の作用と一般の cell 模型比較を構成する。
方針：同じ比較の共役による関手性と、augmentation の可換四角形の自然性を使う。
規約：原 kernel の平坦性は不要。使われ方：一般 cell 模型の単位・合成・比較の整合性。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory
open SSet DifferentialGraded MonoidalClosed
variable (R : Type u) [CommRing R] (D E : Type v)
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
local notation "DC" => _root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.Source R D
local notation "EC" => _root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.Source R E
def dgKernelCellModelFunctorHomObject (P : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R E D) :
    hoFunctor.obj ((ihom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R D)).obj
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R E)) :=
  HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellModuleSourceEquivalence R D).inv ≫
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R DC EC
      (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R EC DC
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellModel R D E (BimoduleCategory.underlying R E D P))) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellModuleSourceEquivalence R E).hom))
def dgKernelCellModelFunctorHomFunctor : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R E D ⥤
    hoFunctor.obj ((ihom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R D)).obj
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R E)) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorOfObjectIsomorphisms (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedFunctorHomFunctor R D E)
    (dgKernelCellModelFunctorHomObject R D E)
    (fun P => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_cellModelIso R D E
      (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R E D P))
def dgKernelCellModelFunctorHomIso :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedFunctorHomFunctor R D E ≅ dgKernelCellModelFunctorHomFunctor R D E :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorOfObjectIsomorphismsIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedFunctorHomFunctor R D E)
    (dgKernelCellModelFunctorHomObject R D E)
    (fun P => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_cellModelIso R D E
      (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R E D P))
lemma dgKernelCellModelFunctorHomIso_app (P : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R E D) :
    (dgKernelCellModelFunctorHomIso R D E).app P =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_cellModelIso R D E
        (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R E D P) := rfl
variable {P0 P1 : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R E D}
local notation "p0" => _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R E D P0
local notation "p1" => _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R E D P1
local notation "FD" => _root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.augmentation R D
local notation "FE" => _root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.augmentation R E
local notation "Q0" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellModel R D E p0
local notation "Q1" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellModel R D E p1
local notation "T0" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellResolution R D E p0
local notation "T1" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellResolution R D E p1
local notation "L" => _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.middleLeftRestrictionFunctor R E D DC FD
local notation "S" => _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.middleRightRestrictionFunctor R E EC DC FE
lemma dgKernelCellModelFunctorHomFunctor_map_raw
    (g : P0 ⟶ P1) (b : Q0 ⟶ Q1)
    (h : b ≫ (T1).π = (T0).π ≫ (S).map ((L).map g)) :
    (dgKernelCellModelFunctorHomFunctor R D E).map g =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R DC EC (BimoduleCategory.underlying R EC DC Q0) ≫
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellModuleSourceEquivalence R E).hom)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R DC EC (BimoduleCategory.underlying R EC DC Q1) ≫
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellModuleSourceEquivalence R E).hom)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellModuleSourceEquivalence R D).inv
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R DC EC (BimoduleCategory.underlying R EC DC Q0))
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R DC EC (BimoduleCategory.underlying R EC DC Q1))
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellModuleSourceEquivalence R E).hom
          ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedFunctorHomFunctor R DC EC).map b)) := by
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorOfObjectIsomorphisms_map_eq_of_square (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedFunctorHomFunctor R D E)
    (dgKernelCellModelFunctorHomObject R D E)
    (fun P => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_cellModelIso R D E
      (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R E D P)) g _
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_cellModelIso_hom_naturality R D E g b h)
end SerrePositivity.InfinityCategories.Project.DerivedCategories
