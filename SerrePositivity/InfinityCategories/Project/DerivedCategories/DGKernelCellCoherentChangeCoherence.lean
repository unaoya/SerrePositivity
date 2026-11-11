module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKernelCellCoherentCompositionChange
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKernelCellCompositionChange
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKernelGeneralCellCoherentLift
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.FunctorIsoIdentityHorizontalSquare
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.FunctorHomPostcompIdentityMap
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.FunctorHomPrecompIdentityMorphism
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
/-!
概要：coherent な実 tensor 模型変更の恒等性・選択独立性・cocycle。
方針：元の二つの合成比較の差という同じ値を使う。
規約：指定比較を変えず、追加の模型圏仮定を置かない。
使われ方：一般 cell 合成の coherence と厳密な模型射。
-/
@[expose] public section
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
lemma dgKernelCellCoherentCompositionChangeIso_eq_original :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellCoherentCompositionChangeIso R D E K m n p0 p1 q0 q1 hm hn
        hM0 hM1 hN0 hN1 hp0 hp1 hq0 hq1 =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellCompositionChangeIso R D E K m n p0 p1 q0 q1 hm hn
        hM0 hM1 hN0 hN1 hp0 hp1 hq0 hq1 := by
  apply Iso.ext
  rfl
include hm hn hM0 hM1 hN0 hN1 hp0 hp1 hq0 hq1 in
lemma dgKernelCellCoherentCompositionChangeIso_independent
    (m' : M0 ⟶ M1) (n' : N0 ⟶ N1)
    (hm' : m' ≫ p1 = p0) (hn' : n' ≫ q1 = q0) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellCoherentCompositionChangeIso R D E K m n p0 p1 q0 q1 hm hn
        hM0 hM1 hN0 hN1 hp0 hp1 hq0 hq1 =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellCoherentCompositionChangeIso R D E K m' n' p0 p1 q0 q1 hm' hn'
        hM0 hM1 hN0 hN1 hp0 hp1 hq0 hq1 :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellCoherentCompositionChangeIso_value R D E K m n p0 p1 q0 q1 hm hn
    hM0 hM1 hN0 hN1 hp0 hp1 hq0 hq1).trans
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellCoherentCompositionChangeIso_value R D E K m' n' p0 p1 q0 q1 hm' hn'
        hM0 hM1 hN0 hN1 hp0 hp1 hq0 hq1).symm
include hM0 hN0 hp0 hq0 in
lemma dgKernelCellCoherentCompositionChangeIso_endo
    (m0 : M0 ⟶ M0) (n0 : N0 ⟶ N0)
    (hm0 : m0 ≫ p0 = p0) (hn0 : n0 ≫ q0 = q0) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellCoherentCompositionChangeIso R D E K m0 n0 p0 p0 q0 q0 hm0 hn0
      hM0 hM0 hN0 hN0 hp0 hp0 hq0 hq0 = Iso.refl _ := by
  simpa only [Iso.symm_self_id] using!
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellCoherentCompositionChangeIso_value R D E K m0 n0 p0 p0 q0 q0 hm0 hn0
      hM0 hM0 hN0 hN0 hp0 hp0 hq0 hq0
include hm hn hM0 hM1 hN0 hN1 hp0 hp1 hq0 hq1 in
lemma dgKernelCellCoherentCompositionChangeIso_cocycle
    {M2 : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R EC DC} {N2 : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R KC EC}
    (p2 : M2 ⟶ (RE).obj ((LD).obj P)) (q2 : N2 ⟶ (RK).obj ((LE).obj Q))
    (m12 : M1 ⟶ M2) (n12 : N1 ⟶ N2) (m02 : M0 ⟶ M2) (n02 : N0 ⟶ N2)
    (hm12 : m12 ≫ p2 = p1) (hn12 : n12 ≫ q2 = q1)
    (hm02 : m02 ≫ p2 = p0) (hn02 : n02 ≫ q2 = q0)
    (hM2 : _root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat R EC DC (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R EC DC M2))
    (hN2 : _root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat R KC EC (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R KC EC N2))
    (hp2 : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.quasiIso R EC DC p2)
    (hq2 : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.quasiIso R KC EC q2) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellCoherentCompositionChangeIso R D E K m n p0 p1 q0 q1 hm hn
        hM0 hM1 hN0 hN1 hp0 hp1 hq0 hq1 ≪≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellCoherentCompositionChangeIso R D E K m12 n12 p1 p2 q1 q2 hm12 hn12
        hM1 hM2 hN1 hN2 hp1 hp2 hq1 hq2 =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellCoherentCompositionChangeIso R D E K m02 n02 p0 p2 q0 q2 hm02 hn02
        hM0 hM2 hN0 hN2 hp0 hp2 hq0 hq2 := by
  let k2 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_compositionCellCoherentLiftIso R D E K
    P Q M2 N2 p2 q2 hM2 hN2 hp2 hq2
  have h01 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellCoherentCompositionChangeIso_value R D E K m n p0 p1 q0 q1 hm hn
    hM0 hM1 hN0 hN1 hp0 hp1 hq0 hq1
  have h12 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellCoherentCompositionChangeIso_value R D E K m12 n12 p1 p2 q1 q2 hm12 hn12
    hM1 hM2 hN1 hN2 hp1 hp2 hq1 hq2
  have h02 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelCellCoherentCompositionChangeIso_value R D E K m02 n02 p0 p2 q0 q2 hm02 hn02
    hM0 hM2 hN0 hN2 hp0 hp2 hq0 hq2
  calc
    _ = ((k0).symm ≪≫ (k1)) ≪≫ ((k1).symm ≪≫ k2) :=
      congrArg₂ Iso.trans h01 h12
    _ = (k0).symm ≪≫ k2 := by simp only [Iso.trans_assoc, Iso.self_symm_id_assoc]
    _ = _ := h02.symm
end SerrePositivity.InfinityCategories.Project.DerivedCategories
