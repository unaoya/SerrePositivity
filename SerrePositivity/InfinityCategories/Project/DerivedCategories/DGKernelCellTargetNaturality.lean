module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKernelCellModelComparison
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKernelTargetModelNaturality
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
variable {P0 P1 : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R E D}
local notation "p0" => _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R E D P0
local notation "p1" => _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R E D P1
local notation "DC" => _root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.Source R D
local notation "EC" => _root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.Source R E
local notation "FD" => _root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.augmentation R D
local notation "FE" => _root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.augmentation R E
local notation "Q0" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellModel R D E p0
local notation "Q1" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellModel R D E p1
local notation "T0" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellResolution R D E p0
local notation "T1" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellResolution R D E p1
local notation "L" => _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.middleLeftRestrictionFunctor R E D DC FD
local notation "S" => _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.middleRightRestrictionFunctor R E EC DC FE
lemma dgKernelCellModel_targetIso_hom_naturality
    (g : P0 ⟶ P1) (b : Q0 ⟶ Q1)
    (h : b ≫ (T1).π = (T0).π ≫ (S).map ((L).map g)) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellModel_targetIso R D E p0).hom ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedFunctorHomFunctor R DC E).map ((L).map g) =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R DC EC (BimoduleCategory.underlying R EC DC Q0))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R DC EC (BimoduleCategory.underlying R EC DC Q1))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellModuleSourceEquivalence R E).hom
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedFunctorHomFunctor R DC EC).map b) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellModel_targetIso R D E p1).hom := by
  have hn := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_targetModelIso_naturality R DC EC E FE
    (T0).π (T1).π ((L).map g) b h
    (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.augmentation_quasiEquivalence R E)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellModel_rightRelativeKFlat R D E p0)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellModel_rightRelativeKFlat R D E p1) (T0).quasiIso (T1).quasiIso
  simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellModel_targetIso, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellModuleSourceEquivalence_hom] using! hn
end SerrePositivity.InfinityCategories.Project.DerivedCategories
