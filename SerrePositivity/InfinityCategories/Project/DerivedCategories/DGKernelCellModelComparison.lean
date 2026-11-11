module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKernelCellModel
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKernelTargetModelInfinity
/-!
概要：任意の元の kernel の実作用を、両端の cell 分解上の指定半自由 kernel の作用へ比較する。
方針：同じ入力 graph 比較と出力 augmentation の全関手比較を、指定入力逆で合成する。
規約：原 Hom の平坦性・原出力の射影性・追加の模型選択を仮定しない。
使われ方：元の一般 kernel の導来合成を平坦模型上で計算する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
variable (R : Type u) [CommRing R] (D E : Type v)
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
/-- 両端を分解した指定 kernel の作用と元の出力 graph の延長は、元の始域制限作用と同型。 -/
def dgKernelCellModel_targetIso (P : _root_.SerrePositivity.DifferentialGraded.Bimodule R E D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R (DGCategoryCellResolution.Source R D)
        (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.Source R E)
        (BimoduleCategory.underlying R _ _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellModel R D E P)) ≫
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellModuleSourceEquivalence R E).hom)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R (DGCategoryCellResolution.Source R D) E
        ((_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.augmentation R D).comp P)) := by
  let ρ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellResolution R D E P
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_targetModelIso R (DGCategoryCellResolution.Source R D)
    (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.Source R E) E (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.augmentation R E)
    (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.of R E (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.Source R D)
      ((_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.augmentation R D).comp P))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellModel R D E P) ρ.π
    (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.augmentation_quasiEquivalence R E)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellModel_rightRelativeKFlat R D E P) ρ.quasiIso
/-- 元の一般 kernel の実作用は、指定入力逆・指定平坦模型の実作用・指定出力同値の合成と同型。 -/
def dgKernelDerivedInfinity_cellModelIso (P : _root_.SerrePositivity.DifferentialGraded.Bimodule R E D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R D E P)
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellModuleSourceEquivalence R D).inv ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R (DGCategoryCellResolution.Source R D)
          (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.Source R E)
          (BimoduleCategory.underlying R _ _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellModel R D E P)) ≫
            (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellModuleSourceEquivalence R E).hom) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_cellSourceIso R D E P ≪≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp (dgKernelCellModel_targetIso R D E P).symm
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellModuleSourceEquivalence R D).inv
end SerrePositivity.InfinityCategories.Project.DerivedCategories
