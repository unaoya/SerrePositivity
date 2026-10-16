module
public import SerrePositivity.DifferentialGraded.Perfect.RingEnhancement
public import SerrePositivity.DifferentialGraded.Perfect.EnhancementLinear
public import SerrePositivity.DifferentialGraded.Perfect.StrictComplexDerivedLinear

/-! # 既存PerfectHomotopyから主PerfへのA線形完全忠実比較

実際のdg比較をH⁰へ降ろし、主射影的enhancementとPerfの既存同値を合成する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A]

/-- 有限射影dg複体のH⁰から主Perfへの実際のdg比較に基づく関手。 -/
def strictPerfectDGComplexToDGPerfect : HomotopyCategory A (StrictPerfectDGComplex A) ⥤
    PerfectModuleCategory A PUnit.{1} :=
  (strictPerfectDGComplexToPerfectDG A).onHomotopy ⋙
    perfectDGModuleToPerfect A PUnit.{1} Set.univ

instance strictPerfectDGComplexToDGPerfectFull : (strictPerfectDGComplexToDGPerfect A).Full := by
  dsimp [strictPerfectDGComplexToDGPerfect]
  infer_instance

instance strictPerfectDGComplexToDGPerfectFaithful :
    (strictPerfectDGComplexToDGPerfect A).Faithful := by
  dsimp [strictPerfectDGComplexToDGPerfect]
  infer_instance

instance strictPerfectDGComplexToDGPerfectAdditive :
    (strictPerfectDGComplexToDGPerfect A).Additive := by
  dsimp [strictPerfectDGComplexToDGPerfect]
  infer_instance

instance strictPerfectDGComplexToDGPerfectLinear :
    (strictPerfectDGComplexToDGPerfect A).Linear A := by
  dsimp [strictPerfectDGComplexToDGPerfect]
  infer_instance

/-- dg包含の可換性をH⁰と主局所化へ送り、既存の主導来比較と照合する。 -/
def strictPerfectDGComplexToPerfectDGCompDerived :
    (strictPerfectDGComplexToPerfectDG A).onHomotopy ⋙
      perfectDGModuleToDerived A PUnit.{1} Set.univ ≅ strictPerfectDGComplexToDerived A := by
  have h : (strictPerfectDGComplexToPerfectDG A).onHomotopy ⋙
      (perfectDGModuleInclusion A PUnit.{1} Set.univ).onHomotopy =
      (strictPerfectDGComplexToRingModule A).onHomotopy :=
    (DGFunctor.onHomotopy_comp (strictPerfectDGComplexToPerfectDG A)
      (perfectDGModuleInclusion A PUnit.{1} Set.univ)).symm.trans
      (congrArg (fun F => DGFunctor.onHomotopy F)
        (strictPerfectDGComplexToPerfectDG_comp_inclusion A))
  exact (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (eqToIso h) (moduleHomotopyToDerivedClosed A PUnit.{1})

/-- 主Perf包含を経由しても、同じ有限射影複体の主導来像となる。 -/
def strictPerfectDGComplexToDGPerfectCompInclusion :
    strictPerfectDGComplexToDGPerfect A ⋙ perfectModuleInclusion A PUnit.{1} Set.univ ≅
      strictPerfectDGComplexToDerived A :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (strictPerfectDGComplexToPerfectDG A).onHomotopy
      (perfectDGModuleToPerfectCompInclusion A PUnit.{1} Set.univ) ≪≫
    strictPerfectDGComplexToPerfectDGCompDerived A

/-- 既存PerfectHomotopyから主PerfへのA線形比較。 -/
def perfectHomotopyToDGPerfect : PerfectHomotopy A ⥤ PerfectModuleCategory A PUnit.{1} :=
  (strictPerfectDGComplexHomotopyEquivalence A).inverse ⋙ strictPerfectDGComplexToDGPerfect A

instance perfectHomotopyToDGPerfectFull : (perfectHomotopyToDGPerfect A).Full := by
  dsimp [perfectHomotopyToDGPerfect]
  infer_instance

instance perfectHomotopyToDGPerfectFaithful : (perfectHomotopyToDGPerfect A).Faithful := by
  dsimp [perfectHomotopyToDGPerfect]
  infer_instance

instance perfectHomotopyToDGPerfectAdditive : (perfectHomotopyToDGPerfect A).Additive := by
  dsimp [perfectHomotopyToDGPerfect]
  infer_instance

instance perfectHomotopyToDGPerfectLinear : (perfectHomotopyToDGPerfect A).Linear A := by
  dsimp [perfectHomotopyToDGPerfect]
  infer_instance

/-- 既存PerfectHomotopyからの主導来比較は主Perf包含を通して自然に因子化する。 -/
def perfectHomotopyToDGPerfectCompInclusion :
    perfectHomotopyToDGPerfect A ⋙ perfectModuleInclusion A PUnit.{1} Set.univ ≅
      perfectHomotopyToDGDerived A :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (strictPerfectDGComplexHomotopyEquivalence A).inverse
      (strictPerfectDGComplexToDGPerfectCompInclusion A)

end SerrePositivity.DifferentialGraded
