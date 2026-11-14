module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.KernelComparisons.DGKernelGeneralCellLiftFactorization
public import
  SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.SimplicialFunctors.FunctorIsoSandwichCompositorNaturality
public import
  SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.KernelComparisons.DGKernelDerivedCompositionHomNaturality
/-!
概要：一般 cell 模型の実合成比較の二変数全射自然性を証明する。
方針：同じ全体比較の自然性と指定 K-flat 合成子の自然性を接続する。
規約：模型の augmentation 正方形は厳密。原 kernel の平坦性は不要。
使われ方：一般 cell 模型の変更と合成の coherence。
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
variable {P0 P1 : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R E D} {Q0 Q1 : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R K E}
  {M0 M1 : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.Source R E) (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.Source
    R D)} {N0 N1 : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.Source R K)
    (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.Source R E)}
  (f : P0 ⟶ P1) (g : Q0 ⟶ Q1) (m : M0 ⟶ M1) (n : N0 ⟶ N1)
  (p0 : M0 ⟶ (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.middleRightRestrictionFunctor R E (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.Source R
    E) (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.Source R D) (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.augmentation R E)).obj
    ((_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.middleLeftRestrictionFunctor R E D (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.Source R D)
    (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.augmentation R D)).obj P0)) (p1 : M1 ⟶
    (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.middleRightRestrictionFunctor R E (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.Source R E)
    (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.Source R D) (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.augmentation R E)).obj
    ((_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.middleLeftRestrictionFunctor R E D (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.Source R D)
    (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.augmentation R D)).obj P1))
  (q0 : N0 ⟶ (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.middleRightRestrictionFunctor R K (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.Source R
    K) (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.Source R E) (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.augmentation R K)).obj
    ((_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.middleLeftRestrictionFunctor R K E (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.Source R E)
    (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.augmentation R E)).obj Q0)) (q1 : N1 ⟶
    (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.middleRightRestrictionFunctor R K (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.Source R K)
    (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.Source R E) (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.augmentation R K)).obj
    ((_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.middleLeftRestrictionFunctor R K E (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.Source R E)
    (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.augmentation R E)).obj Q1))
  (hm : m ≫ p1 = p0 ≫ (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.middleRightRestrictionFunctor R E
    (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.Source R E) (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.Source R D)
    (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.augmentation R E)).map ((_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.middleLeftRestrictionFunctor
    R E D (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.Source R D) (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.augmentation R D)).map f))
  (hn : n ≫ q1 = q0 ≫ (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.middleRightRestrictionFunctor R K
    (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.Source R K) (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.Source R E)
    (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.augmentation R K)).map ((_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.middleLeftRestrictionFunctor
    R K E (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.Source R E) (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.augmentation R E)).map g))
  (hM0 : _root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat R (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.Source R E)
    (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.Source R D) (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R
    (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.Source R E) (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.Source R D) M0))
  (hM1 : _root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat R (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.Source R E)
    (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.Source R D) (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R
    (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.Source R E) (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.Source R D) M1))
  (hN0 : _root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat R (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.Source R K)
    (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.Source R E) (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R
    (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.Source R K) (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.Source R E) N0))
  (hN1 : _root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat R (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.Source R K)
    (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.Source R E) (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R
    (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.Source R K) (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.Source R E) N1))
  (hp0 : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.quasiIso R (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.Source R E)
    (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.Source R D) p0)
  (hp1 : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.quasiIso R (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.Source R E)
    (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.Source R D) p1)
  (hq0 : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.quasiIso R (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.Source R K)
    (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.Source R E) q0)
  (hq1 : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.quasiIso R (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.Source R K)
    (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.Source R E) q1)
local notation "po" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp
local notation "pr" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp
local notation "sd" => _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence.inv (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellModuleSourceEquivalence R D)
local notation "he" => _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence.hom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellModuleSourceEquivalence R E)
local notation "ie" => _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence.inv (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellModuleSourceEquivalence R E)
local notation "tk" => _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence.hom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellModuleSourceEquivalence R K)
local notation "F0" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R D E
  (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R E D P0)
local notation "G0" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R E K
  (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R K E Q0)
local notation "A0" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R DC EC
  (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R EC DC M0)
local notation "B0" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R EC KC
  (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R KC EC N0)
local notation "T0" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R DC KC
  (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.compose R KC EC DC (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R KC EC N0)
    (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R EC DC M0))
local notation "k0" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_compositionCellLiftIso R D E K
  P0 Q0 M0 N0 p0 q0 hM0 hN0 hp0 hq0
local notation "F1" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R D E
  (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R E D P1)
local notation "G1" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R E K
  (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R K E Q1)
local notation "A1" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R DC EC
  (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R EC DC M1)
local notation "B1" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R EC KC
  (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R KC EC N1)
local notation "T1" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R DC KC
  (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.compose R KC EC DC (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R KC EC N1)
    (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R EC DC M1))
local notation "k1" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_compositionCellLiftIso R D E K
  P1 Q1 M1 N1 p1 q1 hM1 hN1 hp1 hq1
local notation "uf" => CategoryTheory.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedFunctorHomFunctor R D E) f
local notation "ug" => CategoryTheory.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedFunctorHomFunctor R E K) g
local notation "um" => CategoryTheory.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedFunctorHomFunctor R DC EC) m
local notation "un" => CategoryTheory.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedFunctorHomFunctor R EC KC) n
local notation "ur" => CategoryTheory.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedFunctorHomFunctor R DC KC)
    (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.composeMap R KC EC DC n m)
include hm hn hM0 hM1 hN0 hN1 hp0 hp1 hq0 hq1 in
lemma dgKernelDerivedInfinity_compositionCellLiftIso_hom_naturality :
    (k0).hom ≫ pr (T0 ≫ tk) (T1 ≫ tk) sd (po T0 T1 tk ur) =
      (po F0 F1 G0 uf ≫ pr G0 G1 F1 ug) ≫ (k1).hom := by
  have ha := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_cellModelLiftIso_hom_naturality R D E
    p0 p1 f m hm hM0 hM1 hp0 hp1
  have hb := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_cellModelLiftIso_hom_naturality R E K
    q0 q1 g n hn hN0 hN1 hq0 hq1
  have hc := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_compIso_hom_naturality R DC EC KC
    m n hM0 hM1 hN0 hN1
  have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIsoSandwichCompositor_hom_naturality sd he ie tk
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellModuleSourceEquivalence R E).homInvIso
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_cellModelLiftIso R D E P0 M0 p0 hM0 hp0)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_cellModelLiftIso R D E P1 M1 p1 hM1 hp1)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_cellModelLiftIso R E K Q0 N0 q0 hN0 hq0)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_cellModelLiftIso R E K Q1 N1 q1 hN1 hq1)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_compIso_of_rightRelativeKFlat R DC EC KC
      (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R EC DC M0)
      (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R KC EC N0) hM0)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_compIso_of_rightRelativeKFlat R DC EC KC
      (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R EC DC M1)
      (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R KC EC N1) hM1)
    uf ug um un ur ha hb hc
  simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_compositionCellLiftIso_factorization] using! h
end SerrePositivity.InfinityCategories.Project.DerivedCategories
