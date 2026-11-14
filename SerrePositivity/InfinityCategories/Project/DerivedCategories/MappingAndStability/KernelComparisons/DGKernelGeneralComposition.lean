module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.KernelComparisons.DGKernelCellComposite
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.FunctorIsoWhiskerComposition
/-!
概要：任意の二 kernel の元の実作用の合成を、指定平坦模型の通常合成の作用へ比較する。
方針：同じ指定模型、実加群圏の比較同型と右相対 K-flat 時の実導来合成を使う。
規約：元の kernel と Hom の平坦性・出力の射影性を仮定しない。
使われ方：一般 kernel の合成と全 coherence。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
variable (R : Type u) [CommRing R] (D E K : Type v)
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R K] [Small.{u} K]
/-- 元の任意二 kernel の実作用の合成は、指定平坦模型の通常合成の実作用と全関手同型。 -/
def dgKernelDerivedInfinity_compositionCellIso
    (P : _root_.SerrePositivity.DifferentialGraded.Bimodule R E D) (Q : _root_.SerrePositivity.DifferentialGraded.Bimodule R K E) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R D E P ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R E K Q)
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellModuleSourceEquivalence R D).inv ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R (DGCategoryCellResolution.Source R D)
          (DGCategoryCellResolution.Source R K) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellComposite R D E K P Q) ≫
            (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellModuleSourceEquivalence R K).hom) := by
  let eD := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellModuleSourceEquivalence R D
  let eE := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellModuleSourceEquivalence R E
  let eK := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellModuleSourceEquivalence R K
  let A := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R (DGCategoryCellResolution.Source R D)
    (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.Source R E)
    (BimoduleCategory.underlying R _ _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellModel R D E P))
  let B := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R (DGCategoryCellResolution.Source R E)
    (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.Source R K)
    (BimoduleCategory.underlying R _ _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellModel R E K Q))
  let C := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R (DGCategoryCellResolution.Source R D)
    (DGCategoryCellResolution.Source R K) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellComposite R D E K P Q)
  have a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R D E P ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R E K Q)
      ((eD.inv ≫ A ≫ eE.hom) ≫ (eE.inv ≫ B ≫ eK.hom)) :=
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_cellModelIso R D E P).postcomp
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R E K Q) ≪≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_cellModelIso R E K Q).precomp (eD.inv ≫ A ≫ eE.hom)
  have b : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      ((eD.inv ≫ A ≫ eE.hom) ≫ (eE.inv ≫ B ≫ eK.hom))
      (eD.inv ≫ A ≫ B ≫ eK.hom) := by
    have h := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp (eE.homInvIso.postcomp (B ≫ eK.hom)) (eD.inv ≫ A)
    simpa only [Category.assoc, Category.id_comp] using! h
  have t : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (A ≫ B) C :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_compIso_of_rightRelativeKFlat R
      (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.Source R D) (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.Source R E)
      (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.Source R K)
      (BimoduleCategory.underlying R _ _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellModel R D E P))
      (BimoduleCategory.underlying R _ _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellModel R E K Q))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellModel_rightRelativeKFlat R D E P)
  have c : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (eD.inv ≫ A ≫ B ≫ eK.hom) (eD.inv ≫ C ≫ eK.hom) := by
    have h := (t.postcomp eK.hom).precomp eD.inv
    simpa only [Category.assoc] using! h
  exact a ≪≫ b ≪≫ c
end SerrePositivity.InfinityCategories.Project.DerivedCategories
