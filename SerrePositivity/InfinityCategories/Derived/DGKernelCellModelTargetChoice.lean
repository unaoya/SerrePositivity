module
public import SerrePositivity.InfinityCategories.Derived.DGKernelTargetModelComparisonValue
public import SerrePositivity.InfinityCategories.Derived.DGKernelCellModelComparison
/-!
概要：指定済みの canonical cell 模型比較を、同じ増大上の別模型の比較へ接続する。
方針：元の出力比較の式を代入し、同じ cell 始域の指定逆で前合成する。
規約：元の比較・指定逆を変更しない。使われ方：一般 cell 模型の選択整合性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet DifferentialGraded DGNerve MonoidalClosed
variable (R : Type u) [CommRing R] (D E : Type v)
  [DGCategory R D] [Small.{u} D] [DGCategory R E] [Small.{u} E]
  (P : Bimodule R E D)
local notation "DC" => DGCategoryCellResolution.Source R D
local notation "EC" => DGCategoryCellResolution.Source R E
local notation "FE" => DGCategoryCellResolution.augmentation R E
local notation "Q0" => dgKernelCellModel R D E P
lemma dgKernelCellModel_targetIso_comparison
    (Q : BimoduleCategory R EC DC)
    (q : Q ⟶ (BimoduleCategory.middleRightRestrictionFunctor R E EC DC FE).obj
      (BimoduleCategory.of R E DC ((DGCategoryCellResolution.augmentation R D).comp P)))
    (b : Q0 ⟶ Q) (h : b ≫ q = ((dgKernelCellResolution R D E P).π))
    (hQ : Bimodule.rightRelativeKFlat R EC DC (BimoduleCategory.underlying R EC DC Q))
    (hq : BimoduleCategory.quasiIso R EC DC q) :
    FunctorIso.postcomp (dgKernelDerivedInfinity_mapIso_of_quasiIso R DC EC b
        (dgKernelTargetModel_map_quasiIso R DC EC E FE ((dgKernelCellResolution R D E P).π) q b h
          (dgKernelCellResolution R D E P).quasiIso hq))
        (dgCellModuleSourceEquivalence R E).hom =
      dgKernelCellModel_targetIso R D E P ≪≫
        (dgKernelDerivedInfinity_targetModelIso R DC EC E FE (BimoduleCategory.of R E DC
          ((DGCategoryCellResolution.augmentation R D).comp P)) Q q
          (DGCategoryCellResolution.augmentation_quasiEquivalence R E) hQ hq).symm := by
  have hh := dgKernelDerivedInfinity_targetModel_comparison_postcomp R DC EC E FE
    ((dgKernelCellResolution R D E P).π) q b h
      (DGCategoryCellResolution.augmentation_quasiEquivalence R E)
    (dgKernelCellModel_rightRelativeKFlat R D E P) hQ
    (dgKernelCellResolution R D E P).quasiIso hq
  simpa only [dgKernelCellModel_targetIso, dgCellModuleSourceEquivalence_hom] using! hh
end SerrePositivity.InfinityCategories
