module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.KernelComparisons.DGKernelCellModelNaturality
/-!
概要：指定済みの cell 比較を保って h Fun 値の作用と一般の cell 模型比較を構成する。
方針：同じ比較の共役による関手性と、augmentation の可換四角形の自然性を使う。
規約：原 kernel の平坦性は不要。使われ方：一般 cell 模型の単位・合成・比較の整合性。
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
local notation "L" => _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.middleLeftRestrictionFunctor R E D DC FD
local notation "S" => _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.middleRightRestrictionFunctor R E EC DC FE
def dgKernelDerivedInfinity_cellModelLiftIso
    (P : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R E D) (Q : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R EC DC)
    (q : Q ⟶ (S).obj ((L).obj P))
    (hQ : _root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat R EC DC (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R EC DC Q))
    (hq : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.quasiIso R EC DC q) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R D E (BimoduleCategory.underlying R E D P))
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellModuleSourceEquivalence R D).inv ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R DC EC (BimoduleCategory.underlying R EC DC Q) ≫
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellModuleSourceEquivalence R E).hom) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_cellSourceIso R D E (BimoduleCategory.underlying R E D P) ≪≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_targetModelIso R DC EC E FE ((L).obj P) Q q
        (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.augmentation_quasiEquivalence R E) hQ hq).symm
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellModuleSourceEquivalence R D).inv
lemma dgKernelDerivedInfinity_cellModelLiftIso_canonical (P : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R E D) :
    dgKernelDerivedInfinity_cellModelLiftIso R D E P
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellModel R D E (BimoduleCategory.underlying R E D P))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellResolution R D E (BimoduleCategory.underlying R E D P)).π
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellModel_rightRelativeKFlat R D E (BimoduleCategory.underlying R E D P))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellResolution R D E (BimoduleCategory.underlying R E D P)).quasiIso =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_cellModelIso R D E (BimoduleCategory.underlying R E D P) := rfl
lemma dgKernelDerivedInfinity_cellModelLiftIso_hom_naturality
    {P0 P1 : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R E D} {Q0 Q1 : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R EC DC}
    (q0 : Q0 ⟶ (S).obj ((L).obj P0)) (q1 : Q1 ⟶ (S).obj ((L).obj P1))
    (g : P0 ⟶ P1) (b : Q0 ⟶ Q1)
    (h : b ≫ q1 = q0 ≫ (S).map ((L).map g))
    (hQ0 : _root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat R EC DC (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R EC DC Q0))
    (hQ1 : _root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat R EC DC (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R EC DC Q1))
    (hq0 : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.quasiIso R EC DC q0)
    (hq1 : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.quasiIso R EC DC q1) :
    (dgKernelDerivedInfinity_cellModelLiftIso R D E P0 Q0 q0 hQ0 hq0).hom ≫
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
          ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedFunctorHomFunctor R DC EC).map b)) =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedFunctorHomFunctor R D E).map g ≫
      (dgKernelDerivedInfinity_cellModelLiftIso R D E P1 Q1 q1 hQ1 hq1).hom := by
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIso_model_hom_naturality_transfer (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellModuleSourceEquivalence R D).inv
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_cellSourceIso R D E (BimoduleCategory.underlying R E D P0))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_cellSourceIso R D E (BimoduleCategory.underlying R E D P1))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_targetModelIso R DC EC E FE ((L).obj P0) Q0 q0
      (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.augmentation_quasiEquivalence R E) hQ0 hq0)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_targetModelIso R DC EC E FE ((L).obj P1) Q1 q1
      (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.augmentation_quasiEquivalence R E) hQ1 hq1)
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedFunctorHomFunctor R D E).map g)
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedFunctorHomFunctor R DC E).map ((L).map g))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R DC EC (BimoduleCategory.underlying R EC DC Q0))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R DC EC (BimoduleCategory.underlying R EC DC Q1))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellModuleSourceEquivalence R E).hom
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedFunctorHomFunctor R DC EC).map b))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_cellSourceIso_hom_naturality R D E g)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_targetModelIso_naturality R DC EC E FE q0 q1
      ((L).map g) b h (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.augmentation_quasiEquivalence R E)
      hQ0 hQ1 hq0 hq1)
end SerrePositivity.InfinityCategories.Project.DerivedCategories
