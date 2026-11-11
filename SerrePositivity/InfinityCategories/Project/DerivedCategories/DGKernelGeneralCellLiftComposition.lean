module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKernelGeneralComposition
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKernelCellModelLift
/-!
概要：一般の許容 cell 模型の通常合成を、元の二つの実作用の合成と比較する。
方針：元の二つの全体比較・中間同値の消去・指定 K-flat 合成子を使う。
規約：原 kernel に平坦性を要求しない。使われ方：模型変更と一般合成の整合性。
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
local notation "DC" => _root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.Source R D
local notation "EC" => _root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.Source R E
local notation "KC" => _root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.Source R K
local notation "LD" => _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.middleLeftRestrictionFunctor R E D DC
  (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.augmentation R D)
local notation "RE" => _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.middleRightRestrictionFunctor R E EC DC
  (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.augmentation R E)
local notation "LE" => _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.middleLeftRestrictionFunctor R K E EC
  (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.augmentation R E)
local notation "RK" => _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.middleRightRestrictionFunctor R K KC EC
  (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.augmentation R K)
def dgKernelDerivedInfinity_compositionCellLiftIso
    (P : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R E D) (Q : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R K E)
    (M : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R EC DC) (N : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R KC EC)
    (p : M ⟶ (RE).obj ((LD).obj P)) (q : N ⟶ (RK).obj ((LE).obj Q))
    (hM : _root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat R EC DC (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R EC DC M))
    (hN : _root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat R KC EC (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R KC EC N))
    (hp : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.quasiIso R EC DC p)
    (hq : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.quasiIso R KC EC q) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R D E (BimoduleCategory.underlying R E D P) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R E K (BimoduleCategory.underlying R K E Q))
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellModuleSourceEquivalence R D).inv ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R (DGCategoryCellResolution.Source R D)
          (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.Source R K) (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.compose R KC EC DC
            (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R KC EC N) (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R EC DC M)) ≫
            (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellModuleSourceEquivalence R K).hom) := by
  let eD := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellModuleSourceEquivalence R D
  let eE := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellModuleSourceEquivalence R E
  let eK := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellModuleSourceEquivalence R K
  let A := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R (DGCategoryCellResolution.Source R D)
    (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.Source R E)
    (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R _ _ M)
  let B := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R (DGCategoryCellResolution.Source R E)
    (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.Source R K)
    (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R _ _ N)
  let C := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R (DGCategoryCellResolution.Source R D)
    (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.Source R K) (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.compose R KC EC DC
      (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R KC EC N) (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R EC DC M))
  have a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R D E (BimoduleCategory.underlying R E D P) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R E K (BimoduleCategory.underlying R K E Q))
      ((eD.inv ≫ A ≫ eE.hom) ≫ (eE.inv ≫ B ≫ eK.hom)) :=
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_cellModelLiftIso R D E P M p hM hp).postcomp
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R E K (BimoduleCategory.underlying R K E Q)) ≪≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_cellModelLiftIso R E K Q N q hN hq).precomp
        (eD.inv ≫ A ≫ eE.hom)
  have b : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      ((eD.inv ≫ A ≫ eE.hom) ≫ (eE.inv ≫ B ≫ eK.hom))
      (eD.inv ≫ A ≫ B ≫ eK.hom) := by
    have h := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp (eE.homInvIso.postcomp (B ≫ eK.hom)) (eD.inv ≫ A)
    simpa only [Category.assoc, Category.id_comp] using! h
  have t : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (A ≫ B) C :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_compIso_of_rightRelativeKFlat R
      (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.Source R D) (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.Source R E)
      (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.Source R K)
      (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R _ _ M)
      (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R _ _ N)
      hM
  have c : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (eD.inv ≫ A ≫ B ≫ eK.hom) (eD.inv ≫ C ≫ eK.hom) := by
    have h := (t.postcomp eK.hom).precomp eD.inv
    simpa only [Category.assoc] using! h
  exact a ≪≫ b ≪≫ c
lemma dgKernelDerivedInfinity_compositionCellLiftIso_canonical
    (P : _root_.SerrePositivity.DifferentialGraded.Bimodule R E D) (Q : _root_.SerrePositivity.DifferentialGraded.Bimodule R K E) :
    dgKernelDerivedInfinity_compositionCellLiftIso R D E K
      (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.of R E D P) (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.of R K E Q)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellModel R D E P) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellModel R E K Q)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellResolution R D E P).π (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellResolution R E K Q).π
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellModel_rightRelativeKFlat R D E P)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellModel_rightRelativeKFlat R E K Q)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellResolution R D E P).quasiIso
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellResolution R E K Q).quasiIso =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_compositionCellIso R D E K P Q := rfl
end SerrePositivity.InfinityCategories.Project.DerivedCategories
