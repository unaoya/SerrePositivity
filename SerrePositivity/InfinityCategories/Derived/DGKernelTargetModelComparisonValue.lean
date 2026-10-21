module
public import SerrePositivity.InfinityCategories.Derived.DGKernelTargetModelComparisonUnitInverse
/-!
概要：元の模型間比較を graph 延長すると、元の二つの出力模型比較の差を回収する。
方針：原 kernel の恒等射に対する自然性と型付き恒等射・指定逆の計算を使う。
規約：元の targetModelIso の値を保つ。使われ方：一般 cell 模型の選択整合性。
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
lemma dgKernelDerivedInfinity_targetModel_comparison_postcomp
    {P : BimoduleCategory R E D} {Q0 Q1 : BimoduleCategory R C D}
    (q0 : Q0 ⟶ (BimoduleCategory.middleRightRestrictionFunctor R E C D F).obj P)
    (q1 : Q1 ⟶ (BimoduleCategory.middleRightRestrictionFunctor R E C D F).obj P)
    (b01 : Q0 ⟶ Q1) (h01 : b01 ≫ q1 = q0) (hF : QuasiEquivalence F)
    (hQ0 : Bimodule.rightRelativeKFlat R C D (BimoduleCategory.underlying R C D Q0))
    (hQ1 : Bimodule.rightRelativeKFlat R C D (BimoduleCategory.underlying R C D Q1))
    (hq0 : BimoduleCategory.quasiIso R C D q0)
    (hq1 : BimoduleCategory.quasiIso R C D q1) :
    FunctorIso.postcomp (dgKernelDerivedInfinity_mapIso_of_quasiIso R D C b01
        (dgKernelTargetModel_map_quasiIso R D C E F q0 q1 b01 h01 hq0 hq1))
        (dgModuleExtensionInfinity R C E F) =
      dgKernelDerivedInfinity_targetModelIso R D C E F P Q0 q0 hF hQ0 hq0 ≪≫
        (dgKernelDerivedInfinity_targetModelIso R D C E F P Q1 q1 hF hQ1 hq1).symm := by
  have hn := dgKernelDerivedInfinity_targetModelIso_naturality R D C E F q0 q1 (𝟙 P) b01
    (by simpa only [CategoryTheory.Functor.map_id, Category.comp_id] using! h01)
    hF hQ0 hQ1 hq0 hq1
  have hi : (dgKernelDerivedFunctorHomFunctor R D E).map (𝟙 P) =
      𝟙 (HomotopyCategory.mk (functorVertex
        (dgKernelDerivedInfinity R D E (BimoduleCategory.underlying R E D P)))) :=
    (dgKernelDerivedFunctorHomFunctor R D E).map_id P
  rw [hi, Category.comp_id] at hn
  apply iso_eq_trans_symm_of_hom_square
  simpa only [functorIso_postcomp_hom_typed, dgKernelDerivedInfinity_comparison_hom] using! hn
end SerrePositivity.InfinityCategories
