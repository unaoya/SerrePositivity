module
public import SerrePositivity.KST.SConstruction.DGRepresentableThickGeneration
public import SerrePositivity.DifferentialGraded.Endomorphism.Perfect
public import SerrePositivity.DifferentialGraded.Morita.QuasiEquivalenceGraph
public import SerrePositivity.DifferentialGraded.Module.Graded

/-! # 指定代表の全 End と元の対象の全 End による Perf 再構成
概要：指定代表が生成する場合、元の dg 対象の全 End で Perf を再構成する。
方針：元の Yoneda の全 Hom 同型と D の End 再構成・準同値 Perf 同値を合成する。
規約：生成条件は明示入力。使われ方：同じ対角商の指定右対象 End。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  (b : D)

/-- 元の指定対象の全 End から、同じ代表加群の全 End への Yoneda の実射。 -/
def dgRepresentableEndMap :
    DGFunctor R (EndomorphismObject b) (EndomorphismObject (representable R b)) :=
  endomorphismMap R (dgYoneda R D) b

/-- 同じ End 上の Yoneda 射は、元の全 Hom 同型による準同値。 -/
lemma dgRepresentableEndMap_quasiEquivalence :
    QuasiEquivalence (dgRepresentableEndMap R D b) := by
  refine ⟨?_, ⟨?_⟩⟩
  · intro x y
    change QuasiIso (dgYonedaIso R b (representable R b)).inv
    infer_instance
  · intro y
    refine ⟨(toHomotopy R (EndomorphismObject b)).obj
      (ForgetEnrichment.of (Complex R) EndomorphismObject.point), ⟨?_⟩⟩
    obtain ⟨y⟩ := y
    cases y using EndomorphismObject.rec
    exact Iso.refl _

/-- 同じ代表の単一生成の下で、元の対象の全 End による実 Perf 同値。 -/
def dgRepresentableEndPerfectEquivalence
    (hgen : modulePerfectOver R D {b} = modulePerfect R D) :
    PerfectModuleCategory R D ≌ PerfectModuleCategory R (EndomorphismObject b) :=
  (perfectEndomorphismEquivalence R D Set.univ (dgRepresentablePerfectPoint R D b)
    (dgRepresentablePerfectPoint_thickGenerates R D b hgen)).trans
    (quasiEquivalencePerfectEquivalence R (EndomorphismObject b)
      (EndomorphismObject (representable R b)) (dgRepresentableEndMap R D b)
      (dgRepresentableEndMap_quasiEquivalence R D b)).symm

end SerrePositivity.KST.SConstruction
