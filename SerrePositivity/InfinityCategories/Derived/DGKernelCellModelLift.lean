module
public import SerrePositivity.InfinityCategories.Derived.DGKernelCellModelNaturality
/-!
概要：指定済みの cell 比較を保って h Fun 値の作用と一般の cell 模型比較を構成する。
方針：同じ比較の共役による関手性と、augmentation の可換四角形の自然性を使う。
規約：原 kernel の平坦性は不要。使われ方：一般 cell 模型の単位・合成・比較の整合性。
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
local notation "DC" => DGCategoryCellResolution.Source R D
local notation "EC" => DGCategoryCellResolution.Source R E
local notation "FD" => DGCategoryCellResolution.augmentation R D
local notation "FE" => DGCategoryCellResolution.augmentation R E
local notation "L" => BimoduleCategory.middleLeftRestrictionFunctor R E D DC FD
local notation "S" => BimoduleCategory.middleRightRestrictionFunctor R E EC DC FE
def dgKernelDerivedInfinity_cellModelLiftIso
    (P : BimoduleCategory R E D) (Q : BimoduleCategory R EC DC)
    (q : Q ⟶ (S).obj ((L).obj P))
    (hQ : Bimodule.rightRelativeKFlat R EC DC (BimoduleCategory.underlying R EC DC Q))
    (hq : BimoduleCategory.quasiIso R EC DC q) :
    FunctorIso (dgKernelDerivedInfinity R D E (BimoduleCategory.underlying R E D P))
      ((dgCellModuleSourceEquivalence R D).inv ≫
        dgKernelDerivedInfinity R DC EC (BimoduleCategory.underlying R EC DC Q) ≫
          (dgCellModuleSourceEquivalence R E).hom) :=
  dgKernelDerivedInfinity_cellSourceIso R D E (BimoduleCategory.underlying R E D P) ≪≫
    FunctorIso.precomp
      (dgKernelDerivedInfinity_targetModelIso R DC EC E FE ((L).obj P) Q q
        (DGCategoryCellResolution.augmentation_quasiEquivalence R E) hQ hq).symm
      (dgCellModuleSourceEquivalence R D).inv
lemma dgKernelDerivedInfinity_cellModelLiftIso_canonical (P : BimoduleCategory R E D) :
    dgKernelDerivedInfinity_cellModelLiftIso R D E P
      (dgKernelCellModel R D E (BimoduleCategory.underlying R E D P))
      (dgKernelCellResolution R D E (BimoduleCategory.underlying R E D P)).π
      (dgKernelCellModel_rightRelativeKFlat R D E (BimoduleCategory.underlying R E D P))
      (dgKernelCellResolution R D E (BimoduleCategory.underlying R E D P)).quasiIso =
    dgKernelDerivedInfinity_cellModelIso R D E (BimoduleCategory.underlying R E D P) := rfl
lemma dgKernelDerivedInfinity_cellModelLiftIso_hom_naturality
    {P0 P1 : BimoduleCategory R E D} {Q0 Q1 : BimoduleCategory R EC DC}
    (q0 : Q0 ⟶ (S).obj ((L).obj P0)) (q1 : Q1 ⟶ (S).obj ((L).obj P1))
    (g : P0 ⟶ P1) (b : Q0 ⟶ Q1)
    (h : b ≫ q1 = q0 ≫ (S).map ((L).map g))
    (hQ0 : Bimodule.rightRelativeKFlat R EC DC (BimoduleCategory.underlying R EC DC Q0))
    (hQ1 : Bimodule.rightRelativeKFlat R EC DC (BimoduleCategory.underlying R EC DC Q1))
    (hq0 : BimoduleCategory.quasiIso R EC DC q0)
    (hq1 : BimoduleCategory.quasiIso R EC DC q1) :
    (dgKernelDerivedInfinity_cellModelLiftIso R D E P0 Q0 q0 hQ0 hq0).hom ≫
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
      (dgKernelDerivedInfinity_cellModelLiftIso R D E P1 Q1 q1 hQ1 hq1).hom := by
  exact functorIso_model_hom_naturality_transfer (dgCellModuleSourceEquivalence R D).inv
    (dgKernelDerivedInfinity_cellSourceIso R D E (BimoduleCategory.underlying R E D P0))
    (dgKernelDerivedInfinity_cellSourceIso R D E (BimoduleCategory.underlying R E D P1))
    (dgKernelDerivedInfinity_targetModelIso R DC EC E FE ((L).obj P0) Q0 q0
      (DGCategoryCellResolution.augmentation_quasiEquivalence R E) hQ0 hq0)
    (dgKernelDerivedInfinity_targetModelIso R DC EC E FE ((L).obj P1) Q1 q1
      (DGCategoryCellResolution.augmentation_quasiEquivalence R E) hQ1 hq1)
    ((dgKernelDerivedFunctorHomFunctor R D E).map g)
    ((dgKernelDerivedFunctorHomFunctor R DC E).map ((L).map g))
    (functorHomPostcomp
      (dgKernelDerivedInfinity R DC EC (BimoduleCategory.underlying R EC DC Q0))
      (dgKernelDerivedInfinity R DC EC (BimoduleCategory.underlying R EC DC Q1))
      (dgCellModuleSourceEquivalence R E).hom
      ((dgKernelDerivedFunctorHomFunctor R DC EC).map b))
    (dgKernelDerivedInfinity_cellSourceIso_hom_naturality R D E g)
    (dgKernelDerivedInfinity_targetModelIso_naturality R DC EC E FE q0 q1
      ((L).map g) b h (DGCategoryCellResolution.augmentation_quasiEquivalence R E)
      hQ0 hQ1 hq0 hq1)
end SerrePositivity.InfinityCategories
