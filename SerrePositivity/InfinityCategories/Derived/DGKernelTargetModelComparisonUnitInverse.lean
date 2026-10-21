module
public import SerrePositivity.InfinityCategories.Derived.DGKernelTargetModelComparisonCocycle
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet DifferentialGraded DGNerve MonoidalClosed
variable (R : Type u) [CommRing R] (D C E : Type v)
  [DGCategory R D] [Small.{u} D] [DGCategory R C] [Small.{u} C]
  [DGCategory R E] [Small.{u} E] (F : DGFunctor R C E)
lemma dgKernelDerivedInfinity_targetModel_comparison_endo
    {P : BimoduleCategory R E D} {Q : BimoduleCategory R C D}
    (q : Q ⟶ (BimoduleCategory.middleRightRestrictionFunctor R E C D F).obj P)
    (b : Q ⟶ Q) (h : b ≫ q = q) (hF : QuasiEquivalence F)
    (hQ : Bimodule.rightRelativeKFlat R C D (BimoduleCategory.underlying R C D Q))
    (hq : BimoduleCategory.quasiIso R C D q) :
    dgKernelDerivedInfinity_mapIso_of_quasiIso R D C b
      (dgKernelTargetModel_map_quasiIso R D C E F q q b h hq hq) = Iso.refl _ := by
  have he := dgKernelDerivedInfinity_targetModel_comparison_independent R D C E F
    q q (𝟙 P) b (𝟙 Q)
    (by simpa only [CategoryTheory.Functor.map_id, Category.comp_id] using! h)
    (by simp only [Category.id_comp, CategoryTheory.Functor.map_id, Category.comp_id])
    hF hQ hQ hq hq
    (dgKernelTargetModel_map_quasiIso R D C E F q q b h hq hq)
    ((BimoduleCategory.quasiIso R C D).id_mem Q)
  exact he.trans (dgKernelDerivedInfinity_comparison_id R D C Q)
lemma dgKernelDerivedInfinity_targetModel_comparison_symm
    {P : BimoduleCategory R E D} {Q0 Q1 : BimoduleCategory R C D}
    (q0 : Q0 ⟶ (BimoduleCategory.middleRightRestrictionFunctor R E C D F).obj P)
    (q1 : Q1 ⟶ (BimoduleCategory.middleRightRestrictionFunctor R E C D F).obj P)
    (b01 : Q0 ⟶ Q1) (b10 : Q1 ⟶ Q0)
    (h01 : b01 ≫ q1 = q0) (h10 : b10 ≫ q0 = q1) (hF : QuasiEquivalence F)
    (hQ1 : Bimodule.rightRelativeKFlat R C D (BimoduleCategory.underlying R C D Q1))
    (hq0 : BimoduleCategory.quasiIso R C D q0)
    (hq1 : BimoduleCategory.quasiIso R C D q1) :
    (dgKernelDerivedInfinity_mapIso_of_quasiIso R D C b01
      (dgKernelTargetModel_map_quasiIso R D C E F q0 q1 b01 h01 hq0 hq1)).symm =
    dgKernelDerivedInfinity_mapIso_of_quasiIso R D C b10
      (dgKernelTargetModel_map_quasiIso R D C E F q1 q0 b10 h10 hq1 hq0) := by
  let e01 := dgKernelDerivedInfinity_mapIso_of_quasiIso R D C b01
    (dgKernelTargetModel_map_quasiIso R D C E F q0 q1 b01 h01 hq0 hq1)
  let e10 := dgKernelDerivedInfinity_mapIso_of_quasiIso R D C b10
    (dgKernelTargetModel_map_quasiIso R D C E F q1 q0 b10 h10 hq1 hq0)
  have hh := dgKernelDerivedInfinity_targetModel_comparison_cocycle R D C E F
    q1 q0 q1 b10 b01 (𝟙 Q1) h10 h01 (by simp only [Category.id_comp])
    hF hQ1 hQ1 hq1 hq0 hq1
  have hp : e10 ≪≫ e01 = Iso.refl _ :=
    hh.trans (dgKernelDerivedInfinity_comparison_id R D C Q1)
  exact iso_symm_eq_of_trans_eq_refl_typed e01 e10 hp
end SerrePositivity.InfinityCategories
