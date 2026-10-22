module
public import SerrePositivity.InfinityCategories.Derived.DGKernelGeneralCellCoherentLift
public import SerrePositivity.InfinityCategories.Derived.FunctorIsoIdentityHorizontalSquare
public import SerrePositivity.InfinityCategories.Derived.FunctorHomPostcompIdentityMap
public import SerrePositivity.InfinityCategories.Derived.FunctorHomPrecompIdentityMorphism
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
lemma dgKernelDerivedInfinity_compositionCellCoherentLiftIso_change_hom :
    (k0).hom ≫ pr (T0 ≫ tk) (T1 ≫ tk) sd (po T0 T1 tk ur) = (k1).hom := by
  have h := dgKernelDerivedInfinity_compositionCellCoherentLiftIso_hom_naturality R D E K
    (𝟙 P) (𝟙 Q) m n p0 p1 q0 q1
    (by simpa only [CategoryTheory.Functor.map_id, Category.comp_id] using hm)
    (by simpa only [CategoryTheory.Functor.map_id, Category.comp_id] using hn)
    hM0 hM1 hN0 hN1 hp0 hp1 hq0 hq1
  exact functorIso_hom_square_of_identity_horizontal F0 G0 (k0) (k1)
    (pr (T0 ≫ tk) (T1 ≫ tk) sd (po T0 T1 tk ur))
    ((dgKernelDerivedFunctorHomFunctor R D E).map (𝟙 P))
    ((dgKernelDerivedFunctorHomFunctor R E K).map (𝟙 Q))
    ((dgKernelDerivedFunctorHomFunctor R D E).map_id P)
    ((dgKernelDerivedFunctorHomFunctor R E K).map_id Q) h
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
def dgKernelCellCoherentCompositionChangeIso : FunctorIso (sd ≫ T0 ≫ tk) (sd ≫ T1 ≫ tk) := by
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
end SerrePositivity.InfinityCategories
