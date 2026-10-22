module
public import SerrePositivity.InfinityCategories.Derived.DGKernelCellSourceNaturality
public import SerrePositivity.InfinityCategories.Derived.DGKernelCellTargetNaturality
public import SerrePositivity.InfinityCategories.Derived.FunctorIsoModelNaturalityTransfer
/-!
概要：同じ指定入力逆・出力比較を用いる元の cell 模型比較全体の自然性を回収する。
方針：元の出力比較の逆四角形を前合成し、元の入力比較の四角形へ接続する。
規約：原 kernel の平坦性は不要。使われ方：canonical cell 模型の射作用の照合。
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
lemma dgKernelDerivedInfinity_cellModelIso_hom_naturality
    (g : P0 ⟶ P1) (b : Q0 ⟶ Q1)
    (h : b ≫ (T1).π = (T0).π ≫ (S).map ((L).map g)) :
    (dgKernelDerivedInfinity_cellModelIso R D E p0).hom ≫
      functorHomPrecomp
        (dgKernelDerivedInfinity R DC EC (BimoduleCategory.underlying R EC DC Q0) ≫
          (dgCellModuleSourceEquivalence R E).hom)
        (dgKernelDerivedInfinity R DC EC (BimoduleCategory.underlying R EC DC Q1) ≫
          (dgCellModuleSourceEquivalence R E).hom)
        (dgCellModuleSourceEquivalence R D).inv
        (functorHomPostcomp
          (dgKernelDerivedInfinity R DC EC (BimoduleCategory.underlying R EC DC Q0))
          (dgKernelDerivedInfinity R DC EC (BimoduleCategory.underlying R EC DC Q1))
          (dgCellModuleSourceEquivalence R E).hom
          ((dgKernelDerivedFunctorHomFunctor R DC EC).map b)) =
    (dgKernelDerivedFunctorHomFunctor R D E).map g ≫
      (dgKernelDerivedInfinity_cellModelIso R D E p1).hom := by
  exact functorIso_model_hom_naturality_transfer (dgCellModuleSourceEquivalence R D).inv
    (dgKernelDerivedInfinity_cellSourceIso R D E p0)
    (dgKernelDerivedInfinity_cellSourceIso R D E p1)
    (dgKernelCellModel_targetIso R D E p0) (dgKernelCellModel_targetIso R D E p1)
    ((dgKernelDerivedFunctorHomFunctor R D E).map g)
    ((dgKernelDerivedFunctorHomFunctor R DC E).map ((L).map g))
    (functorHomPostcomp
      (dgKernelDerivedInfinity R DC EC (BimoduleCategory.underlying R EC DC Q0))
      (dgKernelDerivedInfinity R DC EC (BimoduleCategory.underlying R EC DC Q1))
      (dgCellModuleSourceEquivalence R E).hom
      ((dgKernelDerivedFunctorHomFunctor R DC EC).map b))
    (dgKernelDerivedInfinity_cellSourceIso_hom_naturality R D E g)
    (dgKernelCellModel_targetIso_hom_naturality R D E g b h)
end SerrePositivity.InfinityCategories
