module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.KernelComparisons.DGKernelTargetModelComparisonCocycle
/-!
概要：元の模型比較の自己射は恒等であり、逆向きの比較は指定比較の逆に一致する。
方針：同じ augmentation 上の三模型比較と同型の逆の一意性を使う。
規約：厳密な模型射の恒等・逆一致を仮定しない。使われ方：模型変更の単位・逆整合性。
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
lemma dgKernelDerivedInfinity_targetModel_comparison_endo
    {P : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R E D} {Q : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R C D}
    (q : Q ⟶ (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.middleRightRestrictionFunctor R E C D F).obj P)
    (b : Q ⟶ Q) (h : b ≫ q = q) (hF : _root_.SerrePositivity.DifferentialGraded.QuasiEquivalence F)
    (hQ : _root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat R C D (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R C D Q))
    (hq : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.quasiIso R C D q) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_mapIso_of_quasiIso R D C b
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTargetModel_map_quasiIso R D C E F q q b h hq hq) = Iso.refl _ := by
  have he := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_targetModel_comparison_independent R D C E F
    q q (𝟙 P) b (𝟙 Q)
    (by simpa only [CategoryTheory.Functor.map_id, Category.comp_id] using! h)
    (by simp only [Category.id_comp, CategoryTheory.Functor.map_id, Category.comp_id])
    hF hQ hQ hq hq
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTargetModel_map_quasiIso R D C E F q q b h hq hq)
    ((_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.quasiIso R C D).id_mem Q)
  exact he.trans (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_comparison_id R D C Q)
lemma dgKernelDerivedInfinity_targetModel_comparison_symm
    {P : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R E D} {Q0 Q1 : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R C D}
    (q0 : Q0 ⟶ (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.middleRightRestrictionFunctor R E C D F).obj P)
    (q1 : Q1 ⟶ (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.middleRightRestrictionFunctor R E C D F).obj P)
    (b01 : Q0 ⟶ Q1) (b10 : Q1 ⟶ Q0)
    (h01 : b01 ≫ q1 = q0) (h10 : b10 ≫ q0 = q1) (hF : _root_.SerrePositivity.DifferentialGraded.QuasiEquivalence F)
    (hQ1 : _root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat R C D (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R C D Q1))
    (hq0 : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.quasiIso R C D q0)
    (hq1 : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.quasiIso R C D q1) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_mapIso_of_quasiIso R D C b01
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTargetModel_map_quasiIso R D C E F q0 q1 b01 h01 hq0 hq1)).symm =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_mapIso_of_quasiIso R D C b10
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTargetModel_map_quasiIso R D C E F q1 q0 b10 h10 hq1 hq0) := by
  let e01 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_mapIso_of_quasiIso R D C b01
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTargetModel_map_quasiIso R D C E F q0 q1 b01 h01 hq0 hq1)
  let e10 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_mapIso_of_quasiIso R D C b10
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelTargetModel_map_quasiIso R D C E F q1 q0 b10 h10 hq1 hq0)
  have hh := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_targetModel_comparison_cocycle R D C E F
    q1 q0 q1 b10 b01 (𝟙 Q1) h10 h01 (by simp only [Category.id_comp])
    hF hQ1 hQ1 hq1 hq0 hq1
  have hp : e10 ≪≫ e01 = Iso.refl _ :=
    hh.trans (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_comparison_id R D C Q1)
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.iso_symm_eq_of_trans_eq_refl_typed e01 e10 hp
end SerrePositivity.InfinityCategories.Project.DerivedCategories
