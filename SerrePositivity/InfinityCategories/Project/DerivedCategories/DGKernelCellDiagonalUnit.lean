module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKernelCellDiagonalComparison
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKernelGraphDerivedDiagonalUnit
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.FunctorIsoInverseCellUnit
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKernelCellSourceValue
/-!
概要：canonical diagonal cell 模型の単位を実 span 比較から構成し指定単位へ接続する。
方針：同じ graph の二正方形を指定逆へ移し、実模型比較の値を代入する。
規約：原 Hom の平坦性と旧比較の三角式は仮定しない。使われ方：cell 単位 coherence。
-/
@[expose] public section
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
local notation "DC" => _root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.Source R D
local notation "e" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellModuleSourceEquivalence R D
local notation "f" => _root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.augmentation R D
lemma dgKernelCellDiagonalLiftIso_unit :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellDiagonalLiftIso R D ≪≫
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_identityIso R DC).postcomp (e).hom).precomp (e).inv =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_identityIso R D ≪≫ (e).invHomIso.symm := by
  have hF := _root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.augmentation_quasiEquivalence R D
  have hv := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIso_inverse_cell_unit (e).hom (e).inv (e).invHomIso
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R D D (Bimodule.diagonal R D))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R DC DC (Bimodule.diagonal R DC))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R DC D (functorGraph R DC D f))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_sourceRestrictionIso R DC D D f (Bimodule.diagonal R D))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_targetModelIso R DC DC D f
      (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.of R D DC ((f).comp (_root_.SerrePositivity.DifferentialGraded.Bimodule.diagonal R D)))
      (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.of R DC DC (_root_.SerrePositivity.DifferentialGraded.Bimodule.diagonal R DC))
      (_root_.SerrePositivity.DifferentialGraded.Bimodule.diagonalRestrictionMap R DC D f) hF
      (_root_.SerrePositivity.DifferentialGraded.Bimodule.diagonal_rightRelativeKFlat R DC)
      ((_root_.SerrePositivity.DifferentialGraded.Bimodule.diagonalRestrictionMap_quasiIso_iff R DC D f).2 hF.1))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_graphIso R DC D f)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_identityIso R D) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_identityIso R DC)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_sourceRestrictionIso_diagonal R DC D f)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_targetModelIso_diagonal R DC D f hF)
  have hs : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_cellSourceIso R D D (Bimodule.diagonal R D) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp (e).invHomIso
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R D D (Bimodule.diagonal R D))).symm ≪≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_sourceRestrictionIso R DC D D f (Bimodule.diagonal R D))
          (e).inv := by
    exact eq_of_heq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_cellSourceIso_heq R D D (Bimodule.diagonal R D))
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellDiagonalLiftIso, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_cellModelLiftIso]
  dsimp only [_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying, _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.of]
  rw [hs]
  simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellDiagonalAugmentation,
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_symm, Iso.trans_assoc] using! hv
def dgKernelCellDiagonalUnitIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R DC DC
        (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R DC DC
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellModel R D D (Bimodule.diagonal R D))))
      (𝟙 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R DC)) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellDiagonalComparisonIso R D ≪≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_identityIso R DC
lemma dgKernelCellDiagonalUnitIso_value :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_cellModelIso R D D (Bimodule.diagonal R D) ≪≫
      ((dgKernelCellDiagonalUnitIso R D).postcomp (e).hom).precomp (e).inv =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_identityIso R D ≪≫ (e).invHomIso.symm := by
  simp only [dgKernelCellDiagonalUnitIso, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_trans,
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_trans, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellDiagonalComparisonIso_value,
    Iso.trans_assoc, Iso.self_symm_id_assoc]
  exact dgKernelCellDiagonalLiftIso_unit R D
end
end SerrePositivity.InfinityCategories.Project.DerivedCategories
