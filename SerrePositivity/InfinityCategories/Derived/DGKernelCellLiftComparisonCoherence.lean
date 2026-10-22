module
public import SerrePositivity.InfinityCategories.Derived.DGKernelCellLiftComparison
public import
  SerrePositivity.InfinityCategories.Derived.DGKernelTargetModelComparisonCocycle
/-!
概要：実模型比較の恒等性・選択独立性・二段比較の一致。
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
lemma dgKernelCellLiftComparisonIso_endo
    (P : BimoduleCategory R E D) {Q : BimoduleCategory R EC DC}
    (q : Q ⟶ (S).obj ((L).obj P)) (b : Q ⟶ Q) (h : b ≫ q = q)
    (hQ : Bimodule.rightRelativeKFlat R EC DC (BimoduleCategory.underlying R EC DC Q))
    (hq : BimoduleCategory.quasiIso R EC DC q) :
    dgKernelCellLiftComparisonIso R D E P q q b h hq hq = Iso.refl _ := by
  simpa only [Iso.symm_self_id] using
    dgKernelCellLiftComparisonIso_value R D E P q q b h hQ hQ hq hq
lemma dgKernelCellLiftComparisonIso_independent
    (P : BimoduleCategory R E D) {Q0 Q1 : BimoduleCategory R EC DC}
    (q0 : Q0 ⟶ (S).obj ((L).obj P)) (q1 : Q1 ⟶ (S).obj ((L).obj P))
    (b b' : Q0 ⟶ Q1) (h : b ≫ q1 = q0) (h' : b' ≫ q1 = q0)
    (hQ0 : Bimodule.rightRelativeKFlat R EC DC (BimoduleCategory.underlying R EC DC Q0))
    (hQ1 : Bimodule.rightRelativeKFlat R EC DC (BimoduleCategory.underlying R EC DC Q1))
    (hq0 : BimoduleCategory.quasiIso R EC DC q0)
    (hq1 : BimoduleCategory.quasiIso R EC DC q1) :
    dgKernelCellLiftComparisonIso R D E P q0 q1 b h hq0 hq1 =
      dgKernelCellLiftComparisonIso R D E P q0 q1 b' h' hq0 hq1 :=
  (dgKernelCellLiftComparisonIso_value R D E P q0 q1 b h hQ0 hQ1 hq0 hq1).trans
    (dgKernelCellLiftComparisonIso_value R D E P q0 q1 b' h' hQ0 hQ1 hq0 hq1).symm
lemma dgKernelCellLiftComparisonIso_cocycle
    (P : BimoduleCategory R E D) {Q0 Q1 Q2 : BimoduleCategory R EC DC}
    (q0 : Q0 ⟶ (S).obj ((L).obj P)) (q1 : Q1 ⟶ (S).obj ((L).obj P))
    (q2 : Q2 ⟶ (S).obj ((L).obj P))
    (b01 : Q0 ⟶ Q1) (b12 : Q1 ⟶ Q2) (b02 : Q0 ⟶ Q2)
    (h01 : b01 ≫ q1 = q0) (h12 : b12 ≫ q2 = q1) (h02 : b02 ≫ q2 = q0)
    (hQ0 : Bimodule.rightRelativeKFlat R EC DC (BimoduleCategory.underlying R EC DC Q0))
    (hQ2 : Bimodule.rightRelativeKFlat R EC DC (BimoduleCategory.underlying R EC DC Q2))
    (hq0 : BimoduleCategory.quasiIso R EC DC q0)
    (hq1 : BimoduleCategory.quasiIso R EC DC q1)
    (hq2 : BimoduleCategory.quasiIso R EC DC q2) :
    dgKernelCellLiftComparisonIso R D E P q0 q1 b01 h01 hq0 hq1 ≪≫
        dgKernelCellLiftComparisonIso R D E P q1 q2 b12 h12 hq1 hq2 =
      dgKernelCellLiftComparisonIso R D E P q0 q2 b02 h02 hq0 hq2 := by
  have hc := dgKernelDerivedInfinity_targetModel_comparison_cocycle R DC EC E FE
    q0 q1 q2 b01 b12 b02 h01 h12 h02
    (DGCategoryCellResolution.augmentation_quasiEquivalence R E) hQ0 hQ2 hq0 hq1 hq2
  have ht := congrArg (fun e => FunctorIso.precomp
    (FunctorIso.postcomp e (dgCellModuleSourceEquivalence R E).hom)
    (dgCellModuleSourceEquivalence R D).inv) hc
  simpa only [dgKernelCellLiftComparisonIso, F2.functorIso_postcomp_trans,
    F2.functorIso_precomp_trans] using! ht
end
end SerrePositivity.InfinityCategories
