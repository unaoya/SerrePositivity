module
public import
  SerrePositivity.InfinityCategories.Derived.DGKernelCellLiftComparisonValue
/-!
概要：許容 cell 模型間の実比較と、元の二つの全体比較の差との一致。
方針：augmentation の厳密な可換性と元の全体比較を用いる。
規約：比較を選び直さず、原 kernel に平坦性を課さない。
使われ方：一般 cell 模型の変更 coherence。
-/
@[expose] public section
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet DifferentialGraded DGNerve MonoidalClosed
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] (D E : Type v)
  [DGCategory R D] [Small.{u} D] [DGCategory R E] [Small.{u} E]
local notation "DC" => DGCategoryCellResolution.Source R D
local notation "EC" => DGCategoryCellResolution.Source R E
local notation "FE" => DGCategoryCellResolution.augmentation R E
local notation "L" => BimoduleCategory.middleLeftRestrictionFunctor R E D DC
  (DGCategoryCellResolution.augmentation R D)
local notation "S" => BimoduleCategory.middleRightRestrictionFunctor R E EC DC FE
def dgKernelCellLiftComparisonIso
    (P : BimoduleCategory R E D) {Q0 Q1 : BimoduleCategory R EC DC}
    (q0 : Q0 ⟶ (S).obj ((L).obj P)) (q1 : Q1 ⟶ (S).obj ((L).obj P))
    (b : Q0 ⟶ Q1) (h : b ≫ q1 = q0)
    (hq0 : BimoduleCategory.quasiIso R EC DC q0)
    (hq1 : BimoduleCategory.quasiIso R EC DC q1) :
    FunctorIso
      ((dgCellModuleSourceEquivalence R D).inv ≫
        dgKernelDerivedInfinity R DC EC (BimoduleCategory.underlying R EC DC Q0) ≫
          (dgCellModuleSourceEquivalence R E).hom)
      ((dgCellModuleSourceEquivalence R D).inv ≫
        dgKernelDerivedInfinity R DC EC (BimoduleCategory.underlying R EC DC Q1) ≫
          (dgCellModuleSourceEquivalence R E).hom) :=
  FunctorIso.precomp
    (FunctorIso.postcomp
      (dgKernelDerivedInfinity_mapIso_of_quasiIso R DC EC b
        (dgKernelTargetModel_map_quasiIso R DC EC E FE q0 q1 b h hq0 hq1))
      (dgCellModuleSourceEquivalence R E).hom)
    (dgCellModuleSourceEquivalence R D).inv
lemma dgKernelCellLiftComparisonIso_value
    (P : BimoduleCategory R E D) {Q0 Q1 : BimoduleCategory R EC DC}
    (q0 : Q0 ⟶ (S).obj ((L).obj P)) (q1 : Q1 ⟶ (S).obj ((L).obj P))
    (b : Q0 ⟶ Q1) (h : b ≫ q1 = q0)
    (hQ0 : Bimodule.rightRelativeKFlat R EC DC (BimoduleCategory.underlying R EC DC Q0))
    (hQ1 : Bimodule.rightRelativeKFlat R EC DC (BimoduleCategory.underlying R EC DC Q1))
    (hq0 : BimoduleCategory.quasiIso R EC DC q0)
    (hq1 : BimoduleCategory.quasiIso R EC DC q1) :
    dgKernelCellLiftComparisonIso R D E P q0 q1 b h hq0 hq1 =
      (dgKernelDerivedInfinity_cellModelLiftIso R D E P Q0 q0 hQ0 hq0).symm ≪≫
        dgKernelDerivedInfinity_cellModelLiftIso R D E P Q1 q1 hQ1 hq1 :=
  dgKernelDerivedInfinity_cellModelLift_comparison_value R D E P q0 q1 b h
    hQ0 hQ1 hq0 hq1
end
end SerrePositivity.InfinityCategories
