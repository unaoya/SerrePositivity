module
public import SerrePositivity.DifferentialGraded.Perfect.RingKaroubi
public import SerrePositivity.DifferentialGraded.Perfect.RingPerfectCoherence
public import SerrePositivity.DifferentialGraded.Category.EquivalenceComparison

/-! # Karoubi実現の元の比較への因子化と整数shiftの整合性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory CategoryTheory.Idempotents
variable (A : Type u) [CommRing A]

/-- 元の比較への因子化をtoKaroubiで送ると、既存延長の比較と実現比較の合成になる。 -/
lemma ringPerfectKaroubi_fac_whisker :
    Functor.whiskerRight (ringPerfectKaroubiRealization_fac A).hom
      (toKaroubi (PerfectModuleCategory A PUnit.{1})) =
    (Functor.associator (toKaroubi (PerfectHomotopy A)) (ringPerfectKaroubiRealization A)
      (toKaroubi (PerfectModuleCategory A PUnit.{1}))).hom ≫
    Functor.whiskerLeft (toKaroubi (PerfectHomotopy A))
      (ringPerfectKaroubiRealizationToKaroubiIso A).hom ≫
    ((functorExtension₂CompWhiskeringLeftToKaroubiIso _ _).app
      (perfectHomotopyToDGPerfect A)).hom := by
  exact equivalenceExtension_factor_whisker (toKaroubi (PerfectHomotopy A))
    (ringPerfectKaroubiFunctor A) (perfectHomotopyToDGPerfect A)
    (toKaroubiEquivalence (PerfectModuleCategory A PUnit.{1}))
    ((functorExtension₂CompWhiskeringLeftToKaroubiIso _ _).app
      (perfectHomotopyToDGPerfect A))

/-- 実際のKaroubi実現と元の有限射影比較を結ぶ自然同型は整数shiftと整合する。 -/
instance ringPerfectKaroubiRealizationFacCommShift :
    NatTrans.CommShift (ringPerfectKaroubiRealization_fac A).hom ℤ := by
  refine NatTrans.CommShift.of_comp_faithful
    (G := toKaroubi (PerfectModuleCategory A PUnit.{1})) ?_
  rw [ringPerfectKaroubi_fac_whisker]
  infer_instance

/-- 三角形関手としても、Karoubi実現は元の有限射影比較へ自然に制限する。 -/
def ringPerfectKaroubiRealizationTriangleIso :
    (toKaroubi (PerfectHomotopy A)).mapTriangle ⋙ (ringPerfectKaroubiRealization A).mapTriangle ≅
      (perfectHomotopyToDGPerfect A).mapTriangle :=
  (Functor.mapTriangleCompIso _ _).symm ≪≫
    Functor.mapTriangleIso (ringPerfectKaroubiRealization_fac A)

/-- 主導来包含を経由するKaroubi比較は既存PerfectHomotopyの主導来比較に戻る。 -/
def ringPerfectKaroubiRealizationDerivedIso :
    toKaroubi (PerfectHomotopy A) ⋙
      (ringPerfectKaroubiRealization A ⋙ perfectModuleInclusion A PUnit.{1} Set.univ) ≅
      perfectHomotopyToDGDerived A :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (ringPerfectKaroubiRealization_fac A)
      (perfectModuleInclusion A PUnit.{1} Set.univ) ≪≫
    perfectHomotopyToDGPerfectCompInclusion A

instance ringPerfectKaroubiRealizationDerivedIsoCommShift :
    NatTrans.CommShift (ringPerfectKaroubiRealizationDerivedIso A).hom ℤ := by
  have : NatTrans.CommShift (Functor.isoWhiskerRight (ringPerfectKaroubiRealization_fac A)
      (perfectModuleInclusion A PUnit.{1} Set.univ)).hom ℤ := by
    change NatTrans.CommShift (Functor.whiskerRight (ringPerfectKaroubiRealization_fac A).hom _) ℤ
    infer_instance
  dsimp only [ringPerfectKaroubiRealizationDerivedIso, Iso.trans_hom, Iso.symm_hom]
  infer_instance

end SerrePositivity.DifferentialGraded
