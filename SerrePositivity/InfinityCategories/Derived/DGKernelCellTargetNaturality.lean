module
public import SerrePositivity.InfinityCategories.Derived.DGKernelCellModelComparison
public import SerrePositivity.InfinityCategories.Derived.DGKernelTargetModelNaturality
/-!
概要：指定済みの cell 入出力比較を、その同じ値と任意射の四角形で照合する。
方針：同じ入力同値の指定逆・augmentation・元の全関手比較を保持する。
規約：原 kernel の平坦性を追加しない。使われ方：元の cell 模型比較の自然性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet DifferentialGraded DGNerve MonoidalClosed
variable (R : Type u) [CommRing R] (D E : Type v)
  [DGCategory R D] [Small.{u} D] [DGCategory R E] [Small.{u} E]
variable {P0 P1 : BimoduleCategory R E D}
local notation "p0" => BimoduleCategory.underlying R E D P0
local notation "p1" => BimoduleCategory.underlying R E D P1
local notation "DC" => DGCategoryCellResolution.Source R D
local notation "EC" => DGCategoryCellResolution.Source R E
local notation "FD" => DGCategoryCellResolution.augmentation R D
local notation "FE" => DGCategoryCellResolution.augmentation R E
local notation "Q0" => dgKernelCellModel R D E p0
local notation "Q1" => dgKernelCellModel R D E p1
local notation "T0" => dgKernelCellResolution R D E p0
local notation "T1" => dgKernelCellResolution R D E p1
local notation "L" => BimoduleCategory.middleLeftRestrictionFunctor R E D DC FD
local notation "S" => BimoduleCategory.middleRightRestrictionFunctor R E EC DC FE
lemma dgKernelCellModel_targetIso_hom_naturality
    (g : P0 ⟶ P1) (b : Q0 ⟶ Q1)
    (h : b ≫ (T1).π = (T0).π ≫ (S).map ((L).map g)) :
    (dgKernelCellModel_targetIso R D E p0).hom ≫
      (dgKernelDerivedFunctorHomFunctor R DC E).map ((L).map g) =
    functorHomPostcomp
      (dgKernelDerivedInfinity R DC EC (BimoduleCategory.underlying R EC DC Q0))
      (dgKernelDerivedInfinity R DC EC (BimoduleCategory.underlying R EC DC Q1))
      (dgCellModuleSourceEquivalence R E).hom
      ((dgKernelDerivedFunctorHomFunctor R DC EC).map b) ≫
      (dgKernelCellModel_targetIso R D E p1).hom := by
  have hn := dgKernelDerivedInfinity_targetModelIso_naturality R DC EC E FE
    (T0).π (T1).π ((L).map g) b h
    (DGCategoryCellResolution.augmentation_quasiEquivalence R E)
    (dgKernelCellModel_rightRelativeKFlat R D E p0)
    (dgKernelCellModel_rightRelativeKFlat R D E p1) (T0).quasiIso (T1).quasiIso
  simpa only [dgKernelCellModel_targetIso, dgCellModuleSourceEquivalence_hom] using! hn
end SerrePositivity.InfinityCategories
