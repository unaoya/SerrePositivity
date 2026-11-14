module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.KernelComparisons.DGKernelCellModelLift
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.LocalizationAndRoofs.DGKernelTargetModelMapQuasiIso
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.KernelComparisons.DGKernelDerivedComparisonAction
/-!
概要：許容模型間の実変更同型を、元の二つの全体比較の差へ厳密に同定する。
方針：augmentation の二合成で準同型性を得て、元の全体比較の自然性を同型等式へ移す。
規約：原 kernel に平坦性を課さず比較を選び直さない。使われ方：一般 cell 模型の整合性。
-/
@[expose] public section
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet DifferentialGraded MonoidalClosed
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] (D E : Type v)
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
local notation "DC" => _root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.Source R D
local notation "EC" => _root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.Source R E
local notation "FD" => _root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.augmentation R D
local notation "FE" => _root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.augmentation R E
local notation "L" => _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.middleLeftRestrictionFunctor R E D DC FD
local notation "S" => _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.middleRightRestrictionFunctor R E EC DC FE
lemma dgKernelDerivedInfinity_cellModelLiftIso_change
    (P : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R E D) {Q0 Q1 : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R EC DC}
    (q0 : Q0 ⟶ (S).obj ((L).obj P)) (q1 : Q1 ⟶ (S).obj ((L).obj P))
    (b : Q0 ⟶ Q1) (h : b ≫ q1 = q0)
    (hQ0 : _root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat R EC DC (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R EC DC Q0))
    (hQ1 : _root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat R EC DC (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R EC DC Q1))
    (hq0 : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.quasiIso R EC DC q0)
    (hq1 : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.quasiIso R EC DC q1) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_cellModelLiftIso R D E P Q0 q0 hQ0 hq0 ≪≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_mapIso_of_quasiIso R DC EC b
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTargetModel_map_quasiIso R DC EC E FE q0 q1 b h hq0 hq1))
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellModuleSourceEquivalence R E).hom)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellModuleSourceEquivalence R D).inv =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_cellModelLiftIso R D E P Q1 q1 hQ1 hq1 := by
  have hn := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_cellModelLiftIso_hom_naturality R D E q0 q1
    (𝟙 P) b (by simpa only [CategoryTheory.Functor.map_id, Category.comp_id] using h)
    hQ0 hQ1 hq0 hq1
  rw [CategoryTheory.Functor.map_id] at hn
  apply Iso.ext
  simpa only [Iso.trans_hom, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIso_precomp_hom_typed,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIso_postcomp_hom_typed, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_comparison_hom,
    Category.id_comp] using! hn
lemma dgKernelDerivedInfinity_cellModelLift_comparison_value
    (P : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R E D) {Q0 Q1 : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R EC DC}
    (q0 : Q0 ⟶ (S).obj ((L).obj P)) (q1 : Q1 ⟶ (S).obj ((L).obj P))
    (b : Q0 ⟶ Q1) (h : b ≫ q1 = q0)
    (hQ0 : _root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat R EC DC (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R EC DC Q0))
    (hQ1 : _root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat R EC DC (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R EC DC Q1))
    (hq0 : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.quasiIso R EC DC q0)
    (hq1 : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.quasiIso R EC DC q1) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_mapIso_of_quasiIso R DC EC b
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTargetModel_map_quasiIso R DC EC E FE q0 q1 b h hq0 hq1))
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellModuleSourceEquivalence R E).hom)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellModuleSourceEquivalence R D).inv =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_cellModelLiftIso R D E P Q0 q0 hQ0 hq0).symm ≪≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_cellModelLiftIso R D E P Q1 q1 hQ1 hq1 := by
  have hc := dgKernelDerivedInfinity_cellModelLiftIso_change R D E P q0 q1 b h
    hQ0 hQ1 hq0 hq1
  have ht := congrArg (fun z =>
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_cellModelLiftIso R D E P Q0 q0 hQ0 hq0).symm ≪≫ z) hc
  simpa only [Iso.trans_assoc, Iso.symm_self_id_assoc] using! ht
end
end SerrePositivity.InfinityCategories.Project.DerivedCategories
