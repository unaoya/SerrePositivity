module
public import SerrePositivity.InfinityCategories.Derived.DGKernelCellDiagonalComparison
public import SerrePositivity.InfinityCategories.Derived.DGKernelGraphDerivedDiagonalUnit
public import SerrePositivity.InfinityCategories.Derived.FunctorIsoInverseCellUnit
public import SerrePositivity.InfinityCategories.Derived.DGKernelCellSourceValue
/-!
概要：canonical diagonal cell 模型の単位を実 span 比較から構成し指定単位へ接続する。
方針：同じ graph の二正方形を指定逆へ移し、実模型比較の値を代入する。
規約：原 Hom の平坦性と旧比較の三角式は仮定しない。使われ方：cell 単位 coherence。
-/
@[expose] public section
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
local notation "DC" => DGCategoryCellResolution.Source R D
local notation "e" => dgCellModuleSourceEquivalence R D
local notation "f" => DGCategoryCellResolution.augmentation R D
lemma dgKernelCellDiagonalLiftIso_unit :
    dgKernelCellDiagonalLiftIso R D ≪≫
      ((dgKernelDerivedInfinity_identityIso R DC).postcomp (e).hom).precomp (e).inv =
    dgKernelDerivedInfinity_identityIso R D ≪≫ (e).invHomIso.symm := by
  have hF := DGCategoryCellResolution.augmentation_quasiEquivalence R D
  have hv := functorIso_inverse_cell_unit (e).hom (e).inv (e).invHomIso
    (dgKernelDerivedInfinity R D D (Bimodule.diagonal R D))
    (dgKernelDerivedInfinity R DC DC (Bimodule.diagonal R DC))
    (dgKernelDerivedInfinity R DC D (functorGraph R DC D f))
    (dgKernelDerivedInfinity_sourceRestrictionIso R DC D D f (Bimodule.diagonal R D))
    (dgKernelDerivedInfinity_targetModelIso R DC DC D f
      (BimoduleCategory.of R D DC ((f).comp (Bimodule.diagonal R D)))
      (BimoduleCategory.of R DC DC (Bimodule.diagonal R DC))
      (Bimodule.diagonalRestrictionMap R DC D f) hF
      (Bimodule.diagonal_rightRelativeKFlat R DC)
      ((Bimodule.diagonalRestrictionMap_quasiIso_iff R DC D f).2 hF.1))
    (dgKernelDerivedInfinity_graphIso R DC D f)
    (dgKernelDerivedInfinity_identityIso R D) (dgKernelDerivedInfinity_identityIso R DC)
    (dgKernelDerivedInfinity_sourceRestrictionIso_diagonal R DC D f)
    (dgKernelDerivedInfinity_targetModelIso_diagonal R DC D f hF)
  have hs : dgKernelDerivedInfinity_cellSourceIso R D D (Bimodule.diagonal R D) =
      (FunctorIso.postcomp (e).invHomIso
        (dgKernelDerivedInfinity R D D (Bimodule.diagonal R D))).symm ≪≫
        FunctorIso.precomp
          (dgKernelDerivedInfinity_sourceRestrictionIso R DC D D f (Bimodule.diagonal R D))
          (e).inv := by
    exact eq_of_heq (dgKernelDerivedInfinity_cellSourceIso_heq R D D (Bimodule.diagonal R D))
  simp only [dgKernelCellDiagonalLiftIso, dgKernelDerivedInfinity_cellModelLiftIso]
  dsimp only [BimoduleCategory.underlying, BimoduleCategory.of]
  rw [hs]
  simpa only [dgKernelCellDiagonalAugmentation,
    F2.functorIso_postcomp_symm, Iso.trans_assoc] using! hv
def dgKernelCellDiagonalUnitIso :
    FunctorIso
      (dgKernelDerivedInfinity R DC DC
        (BimoduleCategory.underlying R DC DC
          (dgKernelCellModel R D D (Bimodule.diagonal R D))))
      (𝟙 (dgModuleDerivedInfinityCategory R DC)) :=
  dgKernelCellDiagonalComparisonIso R D ≪≫ dgKernelDerivedInfinity_identityIso R DC
lemma dgKernelCellDiagonalUnitIso_value :
    dgKernelDerivedInfinity_cellModelIso R D D (Bimodule.diagonal R D) ≪≫
      ((dgKernelCellDiagonalUnitIso R D).postcomp (e).hom).precomp (e).inv =
    dgKernelDerivedInfinity_identityIso R D ≪≫ (e).invHomIso.symm := by
  simp only [dgKernelCellDiagonalUnitIso, F2.functorIso_postcomp_trans,
    F2.functorIso_precomp_trans, dgKernelCellDiagonalComparisonIso_value,
    Iso.trans_assoc, Iso.self_symm_id_assoc]
  exact dgKernelCellDiagonalLiftIso_unit R D
end
end SerrePositivity.InfinityCategories
