module
public import SerrePositivity.InfinityCategories.Derived.DGKernelCellCoherentComposition
public import SerrePositivity.InfinityCategories.Derived.DGKernelCellCompositionStrictNaturality
public import SerrePositivity.InfinityCategories.Derived.DGKernelCellCompositionNaturality
public import SerrePositivity.InfinityCategories.Derived.DGKernelCellModelStrictLift
/-!
概要：coherent cell 合成子は任意の原 kernel 射に対し二変数で自然である。
方針：指定 strict lift・augmentation 正方形・元の κ の全射自然性を使う。
規約：原 kernel の平坦性と射の可逆性は不要。使われ方：一般合成の coherence。
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
local notation "P0u" => BimoduleCategory.underlying R E D P0
local notation "CP0" => dgKernelCellModel R D E P0u
local notation "RP0" => dgKernelCellResolution R D E P0u
local notation "Q0u" => BimoduleCategory.underlying R K E Q0
local notation "CQ0" => dgKernelCellModel R E K Q0u
local notation "RQ0" => dgKernelCellResolution R E K Q0u
local notation "F0" => dgKernelDerivedInfinity R D E P0u
local notation "G0" => dgKernelDerivedInfinity R E K Q0u
local notation "T0" => dgKernelDerivedInfinity R DC KC
  (dgKernelCellComposite R D E K P0u Q0u)
local notation "k0" => dgKernelDerivedInfinity_compositionCellCoherentIso R D E K P0u Q0u
local notation "P1u" => BimoduleCategory.underlying R E D P1
local notation "CP1" => dgKernelCellModel R D E P1u
local notation "RP1" => dgKernelCellResolution R D E P1u
local notation "Q1u" => BimoduleCategory.underlying R K E Q1
local notation "CQ1" => dgKernelCellModel R E K Q1u
local notation "RQ1" => dgKernelCellResolution R E K Q1u
local notation "F1" => dgKernelDerivedInfinity R D E P1u
local notation "G1" => dgKernelDerivedInfinity R E K Q1u
local notation "T1" => dgKernelDerivedInfinity R DC KC
  (dgKernelCellComposite R D E K P1u Q1u)
local notation "k1" => dgKernelDerivedInfinity_compositionCellCoherentIso R D E K P1u Q1u
lemma dgKernelDerivedInfinity_compositionCellCoherentIso_hom_naturality
    (f : P0 ⟶ P1) (g : Q0 ⟶ Q1) :
    (k0).hom ≫ functorHomPrecomp
        (T0 ≫ (dgCellModuleSourceEquivalence R K).hom)
        (T1 ≫ (dgCellModuleSourceEquivalence R K).hom)
        (dgCellModuleSourceEquivalence R D).inv
        (functorHomPostcomp T0 T1 (dgCellModuleSourceEquivalence R K).hom
          ((dgKernelDerivedFunctorHomFunctor R DC KC).map
            (BimoduleTensor.composeMap R KC EC DC
              (dgKernelCellModelStrictLift R E K g) (dgKernelCellModelStrictLift R D E f)))) =
      (functorHomPostcomp F0 F1 G0 ((dgKernelDerivedFunctorHomFunctor R D E).map f) ≫
        functorHomPrecomp G0 G1 F1 ((dgKernelDerivedFunctorHomFunctor R E K).map g)) ≫
        (k1).hom := by
  let m := dgKernelCellModelStrictLift R D E f
  let n := dgKernelCellModelStrictLift R E K g
  have ha := dgKernelDerivedInfinity_cellModelIso_hom_naturality R D E f m
    (dgKernelCellModelStrictLift_fac R D E f)
  have hb := dgKernelDerivedInfinity_cellModelIso_hom_naturality R E K g n
    (dgKernelCellModelStrictLift_fac R E K g)
  have hc := dgKernelDerivedInfinity_compIso_hom_naturality R DC EC KC m n
    (dgKernelCellModel_rightRelativeKFlat R D E P0u)
    (dgKernelCellModel_rightRelativeKFlat R D E P1u)
    (dgKernelCellModel_rightRelativeKFlat R E K Q0u)
    (dgKernelCellModel_rightRelativeKFlat R E K Q1u)
  have h := functorIsoSandwichCompositor_hom_naturality
    (F := F0) (F' := F1) (G := G0) (G' := G1)
    (M := dgKernelDerivedInfinity R DC EC (BimoduleCategory.underlying R EC DC CP0))
    (M' := dgKernelDerivedInfinity R DC EC (BimoduleCategory.underlying R EC DC CP1))
    (N := dgKernelDerivedInfinity R EC KC (BimoduleCategory.underlying R KC EC CQ0))
    (N' := dgKernelDerivedInfinity R EC KC (BimoduleCategory.underlying R KC EC CQ1))
    (T := T0) (T' := T1)
    (dgCellModuleSourceEquivalence R D).inv
    (dgCellModuleSourceEquivalence R E).hom
    (dgCellModuleSourceEquivalence R E).inv
    (dgCellModuleSourceEquivalence R K).hom
    (dgCellModuleSourceEquivalence R E).coherentHomInvIso
    (dgKernelDerivedInfinity_cellModelIso R D E P0u)
    (dgKernelDerivedInfinity_cellModelIso R D E P1u)
    (dgKernelDerivedInfinity_cellModelIso R E K Q0u)
    (dgKernelDerivedInfinity_cellModelIso R E K Q1u)
    (dgKernelDerivedInfinity_compIso_of_rightRelativeKFlat R DC EC KC
      (BimoduleCategory.underlying R EC DC CP0) (BimoduleCategory.underlying R KC EC CQ0)
      (dgKernelCellModel_rightRelativeKFlat R D E P0u))
    (dgKernelDerivedInfinity_compIso_of_rightRelativeKFlat R DC EC KC
      (BimoduleCategory.underlying R EC DC CP1) (BimoduleCategory.underlying R KC EC CQ1)
      (dgKernelCellModel_rightRelativeKFlat R D E P1u))
    ((dgKernelDerivedFunctorHomFunctor R D E).map f)
    ((dgKernelDerivedFunctorHomFunctor R E K).map g)
    ((dgKernelDerivedFunctorHomFunctor R DC EC).map m)
    ((dgKernelDerivedFunctorHomFunctor R EC KC).map n)
    ((dgKernelDerivedFunctorHomFunctor R DC KC).map (BimoduleTensor.composeMap R KC EC DC n m))
    ha hb hc
  simpa only [dgKernelDerivedInfinity_compositionCellCoherentIso] using! h
end SerrePositivity.InfinityCategories

