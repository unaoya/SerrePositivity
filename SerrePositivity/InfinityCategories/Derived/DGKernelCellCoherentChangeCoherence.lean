module
public import SerrePositivity.InfinityCategories.Derived.DGKernelCellCoherentCompositionChange
public import SerrePositivity.InfinityCategories.Derived.DGKernelCellCompositionChange
public import SerrePositivity.InfinityCategories.Derived.DGKernelGeneralCellCoherentLift
public import SerrePositivity.InfinityCategories.Derived.FunctorIsoIdentityHorizontalSquare
public import SerrePositivity.InfinityCategories.Derived.FunctorHomPostcompIdentityMap
public import SerrePositivity.InfinityCategories.Derived.FunctorHomPrecompIdentityMorphism
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
variable (R : Type u) [CommRing R] (D E K : Type v)
  [DGCategory R D] [Small.{u} D] [DGCategory R E] [Small.{u} E]
  [DGCategory R K] [Small.{u} K]
local notation "DC" => DGCategoryCellResolution.Source R D
local notation "EC" => DGCategoryCellResolution.Source R E
local notation "KC" => DGCategoryCellResolution.Source R K
local notation "LD" => BimoduleCategory.middleLeftRestrictionFunctor R E D DC
  (DGCategoryCellResolution.augmentation R D)
local notation "RE" => BimoduleCategory.middleRightRestrictionFunctor R E EC DC
  (DGCategoryCellResolution.augmentation R E)
local notation "LE" => BimoduleCategory.middleLeftRestrictionFunctor R K E EC
  (DGCategoryCellResolution.augmentation R E)
local notation "RK" => BimoduleCategory.middleRightRestrictionFunctor R K KC EC
  (DGCategoryCellResolution.augmentation R K)
variable {P : BimoduleCategory R E D} {Q : BimoduleCategory R K E}
  {M0 M1 : BimoduleCategory R (DGCategoryCellResolution.Source R E) (DGCategoryCellResolution.Source
    R D)} {N0 N1 : BimoduleCategory R (DGCategoryCellResolution.Source R K)
    (DGCategoryCellResolution.Source R E)}
  (m : M0 ⟶ M1) (n : N0 ⟶ N1)
  (p0 : M0 ⟶ (BimoduleCategory.middleRightRestrictionFunctor R E (DGCategoryCellResolution.Source R
    E) (DGCategoryCellResolution.Source R D) (DGCategoryCellResolution.augmentation R E)).obj
    ((BimoduleCategory.middleLeftRestrictionFunctor R E D (DGCategoryCellResolution.Source R D)
    (DGCategoryCellResolution.augmentation R D)).obj P)) (p1 : M1 ⟶
    (BimoduleCategory.middleRightRestrictionFunctor R E (DGCategoryCellResolution.Source R E)
    (DGCategoryCellResolution.Source R D) (DGCategoryCellResolution.augmentation R E)).obj
    ((BimoduleCategory.middleLeftRestrictionFunctor R E D (DGCategoryCellResolution.Source R D)
    (DGCategoryCellResolution.augmentation R D)).obj P))
  (q0 : N0 ⟶ (BimoduleCategory.middleRightRestrictionFunctor R K (DGCategoryCellResolution.Source R
    K) (DGCategoryCellResolution.Source R E) (DGCategoryCellResolution.augmentation R K)).obj
    ((BimoduleCategory.middleLeftRestrictionFunctor R K E (DGCategoryCellResolution.Source R E)
    (DGCategoryCellResolution.augmentation R E)).obj Q)) (q1 : N1 ⟶
    (BimoduleCategory.middleRightRestrictionFunctor R K (DGCategoryCellResolution.Source R K)
    (DGCategoryCellResolution.Source R E) (DGCategoryCellResolution.augmentation R K)).obj
    ((BimoduleCategory.middleLeftRestrictionFunctor R K E (DGCategoryCellResolution.Source R E)
    (DGCategoryCellResolution.augmentation R E)).obj Q))
  (hm : m ≫ p1 = p0)
  (hn : n ≫ q1 = q0)
  (hM0 : Bimodule.rightRelativeKFlat R (DGCategoryCellResolution.Source R E)
    (DGCategoryCellResolution.Source R D) (BimoduleCategory.underlying R
    (DGCategoryCellResolution.Source R E) (DGCategoryCellResolution.Source R D) M0))
  (hM1 : Bimodule.rightRelativeKFlat R (DGCategoryCellResolution.Source R E)
    (DGCategoryCellResolution.Source R D) (BimoduleCategory.underlying R
    (DGCategoryCellResolution.Source R E) (DGCategoryCellResolution.Source R D) M1))
  (hN0 : Bimodule.rightRelativeKFlat R (DGCategoryCellResolution.Source R K)
    (DGCategoryCellResolution.Source R E) (BimoduleCategory.underlying R
    (DGCategoryCellResolution.Source R K) (DGCategoryCellResolution.Source R E) N0))
  (hN1 : Bimodule.rightRelativeKFlat R (DGCategoryCellResolution.Source R K)
    (DGCategoryCellResolution.Source R E) (BimoduleCategory.underlying R
    (DGCategoryCellResolution.Source R K) (DGCategoryCellResolution.Source R E) N1))
  (hp0 : BimoduleCategory.quasiIso R (DGCategoryCellResolution.Source R E)
    (DGCategoryCellResolution.Source R D) p0)
  (hp1 : BimoduleCategory.quasiIso R (DGCategoryCellResolution.Source R E)
    (DGCategoryCellResolution.Source R D) p1)
  (hq0 : BimoduleCategory.quasiIso R (DGCategoryCellResolution.Source R K)
    (DGCategoryCellResolution.Source R E) q0)
  (hq1 : BimoduleCategory.quasiIso R (DGCategoryCellResolution.Source R K)
    (DGCategoryCellResolution.Source R E) q1)
local notation "po" => functorHomPostcomp
local notation "pr" => functorHomPrecomp
local notation "sd" => QCatEquivalence.inv (dgCellModuleSourceEquivalence R D)
local notation "he" => QCatEquivalence.hom (dgCellModuleSourceEquivalence R E)
local notation "ie" => QCatEquivalence.inv (dgCellModuleSourceEquivalence R E)
local notation "tk" => QCatEquivalence.hom (dgCellModuleSourceEquivalence R K)
local notation "F0" => dgKernelDerivedInfinity R D E
  (BimoduleCategory.underlying R E D P)
local notation "G0" => dgKernelDerivedInfinity R E K
  (BimoduleCategory.underlying R K E Q)
local notation "A0" => dgKernelDerivedInfinity R DC EC
  (BimoduleCategory.underlying R EC DC M0)
local notation "B0" => dgKernelDerivedInfinity R EC KC
  (BimoduleCategory.underlying R KC EC N0)
local notation "T0" => dgKernelDerivedInfinity R DC KC
  (BimoduleTensor.compose R KC EC DC (BimoduleCategory.underlying R KC EC N0)
    (BimoduleCategory.underlying R EC DC M0))
local notation "k0" => dgKernelDerivedInfinity_compositionCellCoherentLiftIso R D E K
  P Q M0 N0 p0 q0 hM0 hN0 hp0 hq0
local notation "F1" => dgKernelDerivedInfinity R D E
  (BimoduleCategory.underlying R E D P)
local notation "G1" => dgKernelDerivedInfinity R E K
  (BimoduleCategory.underlying R K E Q)
local notation "A1" => dgKernelDerivedInfinity R DC EC
  (BimoduleCategory.underlying R EC DC M1)
local notation "B1" => dgKernelDerivedInfinity R EC KC
  (BimoduleCategory.underlying R KC EC N1)
local notation "T1" => dgKernelDerivedInfinity R DC KC
  (BimoduleTensor.compose R KC EC DC (BimoduleCategory.underlying R KC EC N1)
    (BimoduleCategory.underlying R EC DC M1))
local notation "k1" => dgKernelDerivedInfinity_compositionCellCoherentLiftIso R D E K
  P Q M1 N1 p1 q1 hM1 hN1 hp1 hq1
local notation "um" => CategoryTheory.Functor.map (dgKernelDerivedFunctorHomFunctor R DC EC) m
local notation "un" => CategoryTheory.Functor.map (dgKernelDerivedFunctorHomFunctor R EC KC) n
local notation "ur" => CategoryTheory.Functor.map (dgKernelDerivedFunctorHomFunctor R DC KC)
    (BimoduleTensor.composeMap R KC EC DC n m)
include hm hn hM0 hM1 hN0 hN1 hp0 hp1 hq0 hq1 in
lemma dgKernelCellCoherentCompositionChangeIso_eq_original :
    dgKernelCellCoherentCompositionChangeIso R D E K m n p0 p1 q0 q1 hm hn
        hM0 hM1 hN0 hN1 hp0 hp1 hq0 hq1 =
      dgKernelCellCompositionChangeIso R D E K m n p0 p1 q0 q1 hm hn
        hM0 hM1 hN0 hN1 hp0 hp1 hq0 hq1 := by
  apply Iso.ext
  rfl
include hm hn hM0 hM1 hN0 hN1 hp0 hp1 hq0 hq1 in
lemma dgKernelCellCoherentCompositionChangeIso_independent
    (m' : M0 ⟶ M1) (n' : N0 ⟶ N1)
    (hm' : m' ≫ p1 = p0) (hn' : n' ≫ q1 = q0) :
    dgKernelCellCoherentCompositionChangeIso R D E K m n p0 p1 q0 q1 hm hn
        hM0 hM1 hN0 hN1 hp0 hp1 hq0 hq1 =
      dgKernelCellCoherentCompositionChangeIso R D E K m' n' p0 p1 q0 q1 hm' hn'
        hM0 hM1 hN0 hN1 hp0 hp1 hq0 hq1 :=
  (dgKernelCellCoherentCompositionChangeIso_value R D E K m n p0 p1 q0 q1 hm hn
    hM0 hM1 hN0 hN1 hp0 hp1 hq0 hq1).trans
      (dgKernelCellCoherentCompositionChangeIso_value R D E K m' n' p0 p1 q0 q1 hm' hn'
        hM0 hM1 hN0 hN1 hp0 hp1 hq0 hq1).symm
include hM0 hN0 hp0 hq0 in
lemma dgKernelCellCoherentCompositionChangeIso_endo
    (m0 : M0 ⟶ M0) (n0 : N0 ⟶ N0)
    (hm0 : m0 ≫ p0 = p0) (hn0 : n0 ≫ q0 = q0) :
    dgKernelCellCoherentCompositionChangeIso R D E K m0 n0 p0 p0 q0 q0 hm0 hn0
      hM0 hM0 hN0 hN0 hp0 hp0 hq0 hq0 = Iso.refl _ := by
  simpa only [Iso.symm_self_id] using!
    dgKernelCellCoherentCompositionChangeIso_value R D E K m0 n0 p0 p0 q0 q0 hm0 hn0
      hM0 hM0 hN0 hN0 hp0 hp0 hq0 hq0
include hm hn hM0 hM1 hN0 hN1 hp0 hp1 hq0 hq1 in
lemma dgKernelCellCoherentCompositionChangeIso_cocycle
    {M2 : BimoduleCategory R EC DC} {N2 : BimoduleCategory R KC EC}
    (p2 : M2 ⟶ (RE).obj ((LD).obj P)) (q2 : N2 ⟶ (RK).obj ((LE).obj Q))
    (m12 : M1 ⟶ M2) (n12 : N1 ⟶ N2) (m02 : M0 ⟶ M2) (n02 : N0 ⟶ N2)
    (hm12 : m12 ≫ p2 = p1) (hn12 : n12 ≫ q2 = q1)
    (hm02 : m02 ≫ p2 = p0) (hn02 : n02 ≫ q2 = q0)
    (hM2 : Bimodule.rightRelativeKFlat R EC DC (BimoduleCategory.underlying R EC DC M2))
    (hN2 : Bimodule.rightRelativeKFlat R KC EC (BimoduleCategory.underlying R KC EC N2))
    (hp2 : BimoduleCategory.quasiIso R EC DC p2)
    (hq2 : BimoduleCategory.quasiIso R KC EC q2) :
    dgKernelCellCoherentCompositionChangeIso R D E K m n p0 p1 q0 q1 hm hn
        hM0 hM1 hN0 hN1 hp0 hp1 hq0 hq1 ≪≫
      dgKernelCellCoherentCompositionChangeIso R D E K m12 n12 p1 p2 q1 q2 hm12 hn12
        hM1 hM2 hN1 hN2 hp1 hp2 hq1 hq2 =
      dgKernelCellCoherentCompositionChangeIso R D E K m02 n02 p0 p2 q0 q2 hm02 hn02
        hM0 hM2 hN0 hN2 hp0 hp2 hq0 hq2 := by
  let k2 := dgKernelDerivedInfinity_compositionCellCoherentLiftIso R D E K
    P Q M2 N2 p2 q2 hM2 hN2 hp2 hq2
  have h01 := dgKernelCellCoherentCompositionChangeIso_value R D E K m n p0 p1 q0 q1 hm hn
    hM0 hM1 hN0 hN1 hp0 hp1 hq0 hq1
  have h12 := dgKernelCellCoherentCompositionChangeIso_value R D E K m12 n12 p1 p2 q1 q2 hm12 hn12
    hM1 hM2 hN1 hN2 hp1 hp2 hq1 hq2
  have h02 := dgKernelCellCoherentCompositionChangeIso_value R D E K m02 n02 p0 p2 q0 q2 hm02 hn02
    hM0 hM2 hN0 hN2 hp0 hp2 hq0 hq2
  calc
    _ = ((k0).symm ≪≫ (k1)) ≪≫ ((k1).symm ≪≫ k2) :=
      congrArg₂ Iso.trans h01 h12
    _ = (k0).symm ≪≫ k2 := by simp only [Iso.trans_assoc, Iso.self_symm_id_assoc]
    _ = _ := h02.symm
end SerrePositivity.InfinityCategories
