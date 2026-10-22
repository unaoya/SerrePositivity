module
public import SerrePositivity.InfinityCategories.Derived.DGKernelGeneralCellLiftFactorization
public import
  SerrePositivity.InfinityCategories.Derived.FunctorIsoSandwichCompositorNaturality
public import
  SerrePositivity.InfinityCategories.Derived.DGKernelDerivedCompositionHomNaturality
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
variable {P0 P1 : BimoduleCategory R E D} {Q0 Q1 : BimoduleCategory R K E}
  {M0 M1 : BimoduleCategory R (DGCategoryCellResolution.Source R E) (DGCategoryCellResolution.Source
    R D)} {N0 N1 : BimoduleCategory R (DGCategoryCellResolution.Source R K)
    (DGCategoryCellResolution.Source R E)}
  (f : P0 ⟶ P1) (g : Q0 ⟶ Q1) (m : M0 ⟶ M1) (n : N0 ⟶ N1)
  (p0 : M0 ⟶ (BimoduleCategory.middleRightRestrictionFunctor R E (DGCategoryCellResolution.Source R
    E) (DGCategoryCellResolution.Source R D) (DGCategoryCellResolution.augmentation R E)).obj
    ((BimoduleCategory.middleLeftRestrictionFunctor R E D (DGCategoryCellResolution.Source R D)
    (DGCategoryCellResolution.augmentation R D)).obj P0)) (p1 : M1 ⟶
    (BimoduleCategory.middleRightRestrictionFunctor R E (DGCategoryCellResolution.Source R E)
    (DGCategoryCellResolution.Source R D) (DGCategoryCellResolution.augmentation R E)).obj
    ((BimoduleCategory.middleLeftRestrictionFunctor R E D (DGCategoryCellResolution.Source R D)
    (DGCategoryCellResolution.augmentation R D)).obj P1))
  (q0 : N0 ⟶ (BimoduleCategory.middleRightRestrictionFunctor R K (DGCategoryCellResolution.Source R
    K) (DGCategoryCellResolution.Source R E) (DGCategoryCellResolution.augmentation R K)).obj
    ((BimoduleCategory.middleLeftRestrictionFunctor R K E (DGCategoryCellResolution.Source R E)
    (DGCategoryCellResolution.augmentation R E)).obj Q0)) (q1 : N1 ⟶
    (BimoduleCategory.middleRightRestrictionFunctor R K (DGCategoryCellResolution.Source R K)
    (DGCategoryCellResolution.Source R E) (DGCategoryCellResolution.augmentation R K)).obj
    ((BimoduleCategory.middleLeftRestrictionFunctor R K E (DGCategoryCellResolution.Source R E)
    (DGCategoryCellResolution.augmentation R E)).obj Q1))
  (hm : m ≫ p1 = p0 ≫ (BimoduleCategory.middleRightRestrictionFunctor R E
    (DGCategoryCellResolution.Source R E) (DGCategoryCellResolution.Source R D)
    (DGCategoryCellResolution.augmentation R E)).map ((BimoduleCategory.middleLeftRestrictionFunctor
    R E D (DGCategoryCellResolution.Source R D) (DGCategoryCellResolution.augmentation R D)).map f))
  (hn : n ≫ q1 = q0 ≫ (BimoduleCategory.middleRightRestrictionFunctor R K
    (DGCategoryCellResolution.Source R K) (DGCategoryCellResolution.Source R E)
    (DGCategoryCellResolution.augmentation R K)).map ((BimoduleCategory.middleLeftRestrictionFunctor
    R K E (DGCategoryCellResolution.Source R E) (DGCategoryCellResolution.augmentation R E)).map g))
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
  (BimoduleCategory.underlying R E D P0)
local notation "G0" => dgKernelDerivedInfinity R E K
  (BimoduleCategory.underlying R K E Q0)
local notation "A0" => dgKernelDerivedInfinity R DC EC
  (BimoduleCategory.underlying R EC DC M0)
local notation "B0" => dgKernelDerivedInfinity R EC KC
  (BimoduleCategory.underlying R KC EC N0)
local notation "T0" => dgKernelDerivedInfinity R DC KC
  (BimoduleTensor.compose R KC EC DC (BimoduleCategory.underlying R KC EC N0)
    (BimoduleCategory.underlying R EC DC M0))
local notation "k0" => dgKernelDerivedInfinity_compositionCellLiftIso R D E K
  P0 Q0 M0 N0 p0 q0 hM0 hN0 hp0 hq0
local notation "F1" => dgKernelDerivedInfinity R D E
  (BimoduleCategory.underlying R E D P1)
local notation "G1" => dgKernelDerivedInfinity R E K
  (BimoduleCategory.underlying R K E Q1)
local notation "A1" => dgKernelDerivedInfinity R DC EC
  (BimoduleCategory.underlying R EC DC M1)
local notation "B1" => dgKernelDerivedInfinity R EC KC
  (BimoduleCategory.underlying R KC EC N1)
local notation "T1" => dgKernelDerivedInfinity R DC KC
  (BimoduleTensor.compose R KC EC DC (BimoduleCategory.underlying R KC EC N1)
    (BimoduleCategory.underlying R EC DC M1))
local notation "k1" => dgKernelDerivedInfinity_compositionCellLiftIso R D E K
  P1 Q1 M1 N1 p1 q1 hM1 hN1 hp1 hq1
local notation "uf" => CategoryTheory.Functor.map (dgKernelDerivedFunctorHomFunctor R D E) f
local notation "ug" => CategoryTheory.Functor.map (dgKernelDerivedFunctorHomFunctor R E K) g
local notation "um" => CategoryTheory.Functor.map (dgKernelDerivedFunctorHomFunctor R DC EC) m
local notation "un" => CategoryTheory.Functor.map (dgKernelDerivedFunctorHomFunctor R EC KC) n
local notation "ur" => CategoryTheory.Functor.map (dgKernelDerivedFunctorHomFunctor R DC KC)
    (BimoduleTensor.composeMap R KC EC DC n m)
include hm hn hM0 hM1 hN0 hN1 hp0 hp1 hq0 hq1 in
lemma dgKernelDerivedInfinity_compositionCellLiftIso_hom_naturality :
    (k0).hom ≫ pr (T0 ≫ tk) (T1 ≫ tk) sd (po T0 T1 tk ur) =
      (po F0 F1 G0 uf ≫ pr G0 G1 F1 ug) ≫ (k1).hom := by
  have ha := dgKernelDerivedInfinity_cellModelLiftIso_hom_naturality R D E
    p0 p1 f m hm hM0 hM1 hp0 hp1
  have hb := dgKernelDerivedInfinity_cellModelLiftIso_hom_naturality R E K
    q0 q1 g n hn hN0 hN1 hq0 hq1
  have hc := dgKernelDerivedInfinity_compIso_hom_naturality R DC EC KC
    m n hM0 hM1 hN0 hN1
  have h := functorIsoSandwichCompositor_hom_naturality sd he ie tk
    (dgCellModuleSourceEquivalence R E).homInvIso
    (dgKernelDerivedInfinity_cellModelLiftIso R D E P0 M0 p0 hM0 hp0)
    (dgKernelDerivedInfinity_cellModelLiftIso R D E P1 M1 p1 hM1 hp1)
    (dgKernelDerivedInfinity_cellModelLiftIso R E K Q0 N0 q0 hN0 hq0)
    (dgKernelDerivedInfinity_cellModelLiftIso R E K Q1 N1 q1 hN1 hq1)
    (dgKernelDerivedInfinity_compIso_of_rightRelativeKFlat R DC EC KC
      (BimoduleCategory.underlying R EC DC M0)
      (BimoduleCategory.underlying R KC EC N0) hM0)
    (dgKernelDerivedInfinity_compIso_of_rightRelativeKFlat R DC EC KC
      (BimoduleCategory.underlying R EC DC M1)
      (BimoduleCategory.underlying R KC EC N1) hM1)
    uf ug um un ur ha hb hc
  simpa only [dgKernelDerivedInfinity_compositionCellLiftIso_factorization] using! h
end SerrePositivity.InfinityCategories
