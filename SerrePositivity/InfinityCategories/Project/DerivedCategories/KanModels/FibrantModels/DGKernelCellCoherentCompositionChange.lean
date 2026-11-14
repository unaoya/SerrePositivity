module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.FibrantModels.DGKernelGeneralCellCoherentLift
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.SimplicialFunctors.FunctorIsoIdentityHorizontalSquare
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.SimplicialFunctors.FunctorHomPostcompIdentityMap
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.SimplicialFunctors.FunctorHomPrecompIdentityMorphism
/-!
概要：模型変更の実 tensor 射作用を coherent な合成比較の差に同定する。
方針：全射自然性を原 kernel の恒等射へ適用し、同じ比較を消去する。
規約：augmentation 正方形は厳密。原 kernel の平坦性や模型射の同型性は不要。
使われ方：一般 cell 合成子の模型変更 coherence。
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
variable {P : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R E D} {Q : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R K E}
  {M0 M1 : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.Source R E) (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.Source
    R D)} {N0 N1 : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.Source R K)
    (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.Source R E)}
  (m : M0 ⟶ M1) (n : N0 ⟶ N1)
  (p0 : M0 ⟶ (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.middleRightRestrictionFunctor R E (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.Source R
    E) (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.Source R D) (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.augmentation R E)).obj
    ((_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.middleLeftRestrictionFunctor R E D (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.Source R D)
    (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.augmentation R D)).obj P)) (p1 : M1 ⟶
    (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.middleRightRestrictionFunctor R E (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.Source R E)
    (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.Source R D) (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.augmentation R E)).obj
    ((_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.middleLeftRestrictionFunctor R E D (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.Source R D)
    (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.augmentation R D)).obj P))
  (q0 : N0 ⟶ (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.middleRightRestrictionFunctor R K (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.Source R
    K) (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.Source R E) (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.augmentation R K)).obj
    ((_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.middleLeftRestrictionFunctor R K E (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.Source R E)
    (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.augmentation R E)).obj Q)) (q1 : N1 ⟶
    (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.middleRightRestrictionFunctor R K (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.Source R K)
    (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.Source R E) (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.augmentation R K)).obj
    ((_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.middleLeftRestrictionFunctor R K E (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.Source R E)
    (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.augmentation R E)).obj Q))
  (hm : m ≫ p1 = p0)
  (hn : n ≫ q1 = q0)
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
  (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R E D P)
local notation "G0" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R E K
  (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R K E Q)
local notation "A0" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R DC EC
  (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R EC DC M0)
local notation "B0" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R EC KC
  (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R KC EC N0)
local notation "T0" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R DC KC
  (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.compose R KC EC DC (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R KC EC N0)
    (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R EC DC M0))
local notation "k0" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_compositionCellCoherentLiftIso R D E K
  P Q M0 N0 p0 q0 hM0 hN0 hp0 hq0
local notation "F1" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R D E
  (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R E D P)
local notation "G1" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R E K
  (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R K E Q)
local notation "A1" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R DC EC
  (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R EC DC M1)
local notation "B1" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R EC KC
  (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R KC EC N1)
local notation "T1" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R DC KC
  (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.compose R KC EC DC (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R KC EC N1)
    (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R EC DC M1))
local notation "k1" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_compositionCellCoherentLiftIso R D E K
  P Q M1 N1 p1 q1 hM1 hN1 hp1 hq1
local notation "um" => CategoryTheory.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedFunctorHomFunctor R DC EC) m
local notation "un" => CategoryTheory.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedFunctorHomFunctor R EC KC) n
local notation "ur" => CategoryTheory.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedFunctorHomFunctor R DC KC)
    (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.composeMap R KC EC DC n m)
include hm hn hM0 hM1 hN0 hN1 hp0 hp1 hq0 hq1 in
lemma dgKernelDerivedInfinity_compositionCellCoherentLiftIso_change_hom :
    (k0).hom ≫ pr (T0 ≫ tk) (T1 ≫ tk) sd (po T0 T1 tk ur) = (k1).hom := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_compositionCellCoherentLiftIso_hom_naturality R D E K
    (𝟙 P) (𝟙 Q) m n p0 p1 q0 q1
    (by simpa only [CategoryTheory.Functor.map_id, Category.comp_id] using hm)
    (by simpa only [CategoryTheory.Functor.map_id, Category.comp_id] using hn)
    hM0 hM1 hN0 hN1 hp0 hp1 hq0 hq1
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIso_hom_square_of_identity_horizontal F0 G0 (k0) (k1)
    (pr (T0 ≫ tk) (T1 ≫ tk) sd (po T0 T1 tk ur))
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedFunctorHomFunctor R D E).map (𝟙 P))
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedFunctorHomFunctor R E K).map (𝟙 Q))
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedFunctorHomFunctor R D E).map_id P)
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedFunctorHomFunctor R E K).map_id Q) h
include hm hn hM0 hM1 hN0 hN1 hp0 hp1 hq0 hq1 in
lemma dgKernelDerivedInfinity_compositionCellCoherentLiftIso_change_value :
    pr (T0 ≫ tk) (T1 ≫ tk) sd (po T0 T1 tk ur) = (k0).inv ≫ (k1).hom := by
  have h := dgKernelDerivedInfinity_compositionCellCoherentLiftIso_change_hom R D E K
    m n p0 p1 q0 q1 hm hn hM0 hM1 hN0 hN1 hp0 hp1 hq0 hq1
  exact (Iso.eq_inv_comp (k0)).mpr h
include hm hn hM0 hM1 hN0 hN1 hp0 hp1 hq0 hq1 in
lemma dgKernelDerivedInfinity_compositionCellCoherentLiftIso_change_isIso :
    IsIso (pr (T0 ≫ tk) (T1 ≫ tk) sd (po T0 T1 tk ur)) := by
  rw [dgKernelDerivedInfinity_compositionCellCoherentLiftIso_change_value R D E K
    m n p0 p1 q0 q1 hm hn hM0 hM1 hN0 hN1 hp0 hp1 hq0 hq1]
  infer_instance
def dgKernelCellCoherentCompositionChangeIso : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (sd ≫ T0 ≫ tk) (sd ≫ T1 ≫ tk) := by
  letI := dgKernelDerivedInfinity_compositionCellCoherentLiftIso_change_isIso R D E K
    m n p0 p1 q0 q1 hm hn hM0 hM1 hN0 hN1 hp0 hp1 hq0 hq1
  exact asIso (pr (T0 ≫ tk) (T1 ≫ tk) sd (po T0 T1 tk ur))
include hm hn hM0 hM1 hN0 hN1 hp0 hp1 hq0 hq1 in
lemma dgKernelCellCoherentCompositionChangeIso_value :
    dgKernelCellCoherentCompositionChangeIso R D E K m n p0 p1 q0 q1 hm hn
      hM0 hM1 hN0 hN1 hp0 hp1 hq0 hq1 = (k0).symm ≪≫ (k1) := by
  apply Iso.ext
  exact dgKernelDerivedInfinity_compositionCellCoherentLiftIso_change_value R D E K
    m n p0 p1 q0 q1 hm hn hM0 hM1 hN0 hN1 hp0 hp1 hq0 hq1
end SerrePositivity.InfinityCategories.Project.DerivedCategories
