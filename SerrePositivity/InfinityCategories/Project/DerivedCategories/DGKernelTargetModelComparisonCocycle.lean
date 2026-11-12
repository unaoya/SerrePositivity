module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKernelTargetModelChoiceIndependence
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKernelTargetModelMapQuasiIso
/-!
概要：同じ原 kernel へ増大する模型の比較は、直接選択と二段合成で一致する。
方針：実 augmentation の二合成から準同型性を回収し、指定比較の選択独立性を使う。
規約：指定比較を再選択しない。使われ方：一般 cell 模型の合成整合性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet DifferentialGraded MonoidalClosed
variable (R : Type u) [CommRing R] (D C E : Type v)
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D] [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [Small.{u} C]
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E] (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C E)
lemma dgKernelDerivedInfinity_targetModel_comparison_cocycle
    {P : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R E D} {Q0 Q1 Q2 : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R C D}
    (q0 : Q0 ⟶ (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.middleRightRestrictionFunctor R E C D F).obj P)
    (q1 : Q1 ⟶ (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.middleRightRestrictionFunctor R E C D F).obj P)
    (q2 : Q2 ⟶ (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.middleRightRestrictionFunctor R E C D F).obj P)
    (b01 : Q0 ⟶ Q1) (b12 : Q1 ⟶ Q2) (b02 : Q0 ⟶ Q2)
    (h01 : b01 ≫ q1 = q0) (h12 : b12 ≫ q2 = q1) (h02 : b02 ≫ q2 = q0)
    (hF : _root_.SerrePositivity.DifferentialGraded.QuasiEquivalence F)
    (hQ0 : _root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat R C D (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R C D Q0))
    (hQ2 : _root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat R C D (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R C D Q2))
    (hq0 : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.quasiIso R C D q0)
    (hq1 : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.quasiIso R C D q1)
    (hq2 : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.quasiIso R C D q2) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_mapIso_of_quasiIso R D C b01
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTargetModel_map_quasiIso R D C E F q0 q1 b01 h01 hq0 hq1) ≪≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_mapIso_of_quasiIso R D C b12
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTargetModel_map_quasiIso R D C E F q1 q2 b12 h12 hq1 hq2) =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_mapIso_of_quasiIso R D C b02
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTargetModel_map_quasiIso R D C E F q0 q2 b02 h02 hq0 hq2) := by
  have hb01 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTargetModel_map_quasiIso R D C E F q0 q1 b01 h01 hq0 hq1
  have hb12 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTargetModel_map_quasiIso R D C E F q1 q2 b12 h12 hq1 hq2
  have hb02 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTargetModel_map_quasiIso R D C E F q0 q2 b02 h02 hq0 hq2
  rw [← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_comparison_comp R D C b01 b12 hb01 hb12]
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_targetModel_comparison_independent R D C E F
    q0 q2 (𝟙 P) (b01 ≫ b12) b02 _ _ hF hQ0 hQ2 hq0 hq2
      ((_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.quasiIso R C D).comp_mem b01 b12 hb01 hb12) hb02
  · simp only [Category.assoc, h12, h01, CategoryTheory.Functor.map_id, Category.comp_id]
  · simp only [CategoryTheory.Functor.map_id, Category.comp_id, h02]
end SerrePositivity.InfinityCategories.Project.DerivedCategories
