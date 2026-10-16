module
public import SerrePositivity.DifferentialGraded.Perfect.RingPerfectTriangulated
public import SerrePositivity.DifferentialGraded.Perfect.RingFiniteCellImage

/-! # 主Perfの対象は既存有限射影ホモトピー圏の比較像のretract

finite cellの実際の評価複体を使ってretractの上の対象を既存PerfectHomotopyで表す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex
variable (A : Type u) [CommRing A]
local instance : HasDerivedCategory.{u + 1} (ModuleCat.{u} A) := HasDerivedCategory.standard _

/-- 一対象Aの有限cellの評価を既存PerfectHomotopyの実際の対象にする。 -/
def ringFiniteCellPerfectHomotopy (M : ModuleCategory A PUnit.{1})
    (hM : moduleFiniteCell A PUnit.{1} M) : PerfectHomotopy A :=
  ⟨(_root_.HomotopyCategory.quotient (ModuleCat.{u} A) (.up ℤ)).obj
      ((moduleEvaluation A PUnit.{1} PUnit.unit).obj M),
    (perfectHomotopyProperty_quotient A _).2
      (moduleFiniteCell_ringEvaluation_strictlyPerfect A hM)⟩

/-- この既存有限射影対象の主導来比較は、元の有限cellの主局所化像と同型。 -/
def ringFiniteCellPerfectHomotopyDerivedIso (M : ModuleCategory A PUnit.{1})
    (hM : moduleFiniteCell A PUnit.{1} M) :
    (perfectHomotopyToDGDerived A).obj (ringFiniteCellPerfectHomotopy A M hM) ≅
      (moduleToDerived A PUnit.{1}).obj M := by
  let P : Complex A := (moduleEvaluation A PUnit.{1} PUnit.unit).obj M
  let e : (moduleToDerived A PUnit.{1}).obj ((complexToRingModule A).obj P) ≅
      (moduleToDerived A PUnit.{1}).obj M := eqToIso (congrArg
    (fun N => (moduleToDerived A PUnit.{1}).obj (ForgetEnrichment.of (Complex A) N))
      (ringModule_recover A (ForgetEnrichment.to (Complex A) M)))
  exact (perfectHomotopyToDGDerivedCanonicalIso A).app (ringFiniteCellPerfectHomotopy A M hM) ≪≫
    (ringDerivedEquivalence A).inverse.mapIso
      ((DerivedCategory.quotientCompQhIso (ModuleCat.{u} A)).app P) ≪≫
    ringComplexDerivedUnitIso A P ≪≫ e

/-- 主Perfの全対象は、既存PerfectHomotopyからの実際の比較像のretractである。 -/
lemma perfectModule_ring_retract_of_perfectHomotopy (X : PerfectModuleCategory A PUnit.{1}) :
    ∃ P : PerfectHomotopy A, Nonempty (Retract X ((perfectHomotopyToDGPerfect A).obj P)) := by
  obtain ⟨M, hM, ⟨r⟩⟩ := (modulePerfect_iff A PUnit.{1} X.obj).1 X.property
  let P := ringFiniteCellPerfectHomotopy A M hM
  let e : ((perfectHomotopyToDGPerfect A).obj P).obj ≅
      (moduleToDerived A PUnit.{1}).obj M :=
    (perfectHomotopyToDGPerfectCompInclusion A).app P ≪≫
      ringFiniteCellPerfectHomotopyDerivedIso A M hM
  let r' := r.trans (Retract.ofIso e.symm)
  refine ⟨P, ⟨{ i := ObjectProperty.homMk r'.i
                r := ObjectProperty.homMk r'.r
                retract := ?_ }⟩⟩
  exact (modulePerfect A PUnit.{1}).hom_ext r'.retract

end SerrePositivity.DifferentialGraded
