module
public import SerrePositivity.InfinityCategories.Derived.DGKernelGeneralComposition
public import SerrePositivity.InfinityCategories.Derived.DGKernelCellModelLift
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
def dgKernelDerivedInfinity_compositionCellLiftIso
    (P : BimoduleCategory R E D) (Q : BimoduleCategory R K E)
    (M : BimoduleCategory R EC DC) (N : BimoduleCategory R KC EC)
    (p : M ⟶ (RE).obj ((LD).obj P)) (q : N ⟶ (RK).obj ((LE).obj Q))
    (hM : Bimodule.rightRelativeKFlat R EC DC (BimoduleCategory.underlying R EC DC M))
    (hN : Bimodule.rightRelativeKFlat R KC EC (BimoduleCategory.underlying R KC EC N))
    (hp : BimoduleCategory.quasiIso R EC DC p)
    (hq : BimoduleCategory.quasiIso R KC EC q) :
    FunctorIso
      (dgKernelDerivedInfinity R D E (BimoduleCategory.underlying R E D P) ≫
        dgKernelDerivedInfinity R E K (BimoduleCategory.underlying R K E Q))
      ((dgCellModuleSourceEquivalence R D).inv ≫
        dgKernelDerivedInfinity R (DGCategoryCellResolution.Source R D)
          (DGCategoryCellResolution.Source R K) (BimoduleTensor.compose R KC EC DC
            (BimoduleCategory.underlying R KC EC N) (BimoduleCategory.underlying R EC DC M)) ≫
            (dgCellModuleSourceEquivalence R K).hom) := by
  let eD := dgCellModuleSourceEquivalence R D
  let eE := dgCellModuleSourceEquivalence R E
  let eK := dgCellModuleSourceEquivalence R K
  let A := dgKernelDerivedInfinity R (DGCategoryCellResolution.Source R D)
    (DGCategoryCellResolution.Source R E)
    (BimoduleCategory.underlying R _ _ M)
  let B := dgKernelDerivedInfinity R (DGCategoryCellResolution.Source R E)
    (DGCategoryCellResolution.Source R K)
    (BimoduleCategory.underlying R _ _ N)
  let C := dgKernelDerivedInfinity R (DGCategoryCellResolution.Source R D)
    (DGCategoryCellResolution.Source R K) (BimoduleTensor.compose R KC EC DC
      (BimoduleCategory.underlying R KC EC N) (BimoduleCategory.underlying R EC DC M))
  have a : FunctorIso
      (dgKernelDerivedInfinity R D E (BimoduleCategory.underlying R E D P) ≫
        dgKernelDerivedInfinity R E K (BimoduleCategory.underlying R K E Q))
      ((eD.inv ≫ A ≫ eE.hom) ≫ (eE.inv ≫ B ≫ eK.hom)) :=
    (dgKernelDerivedInfinity_cellModelLiftIso R D E P M p hM hp).postcomp
      (dgKernelDerivedInfinity R E K (BimoduleCategory.underlying R K E Q)) ≪≫
      (dgKernelDerivedInfinity_cellModelLiftIso R E K Q N q hN hq).precomp
        (eD.inv ≫ A ≫ eE.hom)
  have b : FunctorIso
      ((eD.inv ≫ A ≫ eE.hom) ≫ (eE.inv ≫ B ≫ eK.hom))
      (eD.inv ≫ A ≫ B ≫ eK.hom) := by
    have h := FunctorIso.precomp (eE.homInvIso.postcomp (B ≫ eK.hom)) (eD.inv ≫ A)
    simpa only [Category.assoc, Category.id_comp] using! h
  have t : FunctorIso (A ≫ B) C :=
    dgKernelDerivedInfinity_compIso_of_rightRelativeKFlat R
      (DGCategoryCellResolution.Source R D) (DGCategoryCellResolution.Source R E)
      (DGCategoryCellResolution.Source R K)
      (BimoduleCategory.underlying R _ _ M)
      (BimoduleCategory.underlying R _ _ N)
      hM
  have c : FunctorIso (eD.inv ≫ A ≫ B ≫ eK.hom) (eD.inv ≫ C ≫ eK.hom) := by
    have h := (t.postcomp eK.hom).precomp eD.inv
    simpa only [Category.assoc] using! h
  exact a ≪≫ b ≪≫ c
lemma dgKernelDerivedInfinity_compositionCellLiftIso_canonical
    (P : Bimodule R E D) (Q : Bimodule R K E) :
    dgKernelDerivedInfinity_compositionCellLiftIso R D E K
      (BimoduleCategory.of R E D P) (BimoduleCategory.of R K E Q)
      (dgKernelCellModel R D E P) (dgKernelCellModel R E K Q)
      (dgKernelCellResolution R D E P).π (dgKernelCellResolution R E K Q).π
      (dgKernelCellModel_rightRelativeKFlat R D E P)
      (dgKernelCellModel_rightRelativeKFlat R E K Q)
      (dgKernelCellResolution R D E P).quasiIso
      (dgKernelCellResolution R E K Q).quasiIso =
    dgKernelDerivedInfinity_compositionCellIso R D E K P Q := rfl
end SerrePositivity.InfinityCategories
