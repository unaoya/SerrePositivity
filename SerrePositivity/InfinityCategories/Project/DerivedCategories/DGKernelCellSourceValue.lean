module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKernelCellSourceComparison
/-!
概要：指定済みの cell 入出力比較を、その同じ値と任意射の四角形で照合する。
方針：同じ入力同値の指定逆・augmentation・元の全関手比較を保持する。
規約：原 kernel の平坦性を追加しない。使われ方：元の cell 模型比較の自然性。
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
lemma dgKernelDerivedInfinity_cellSourceIso_heq (P : _root_.SerrePositivity.DifferentialGraded.Bimodule R E D) :
    HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_cellSourceIso R D E P)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellModuleSourceEquivalence R D).invHomIso
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R D E P)).symm ≪≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_sourceRestrictionIso R
            (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.Source R D) D E
            (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.augmentation R D) P)
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellModuleSourceEquivalence R D).inv) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_cellSourceIso]
  rfl
end SerrePositivity.InfinityCategories.Project.DerivedCategories
