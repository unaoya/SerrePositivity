module
public import SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonRestriction
public import SerrePositivity.DifferentialGraded.Derived.AcyclicZero
public import SerrePositivity.InfinityCategories.Derived.DGStableHomotopyEquivalence
public import SerrePositivity.InfinityCategories.Derived.DGPerfectModulesInfinity
/-!
概要：小さい dg 圏の全対象商の Perf では、全ての native 頂点が零対象である。
方針：商の指定収縮から全加群の acyclic 性を得て、Perf の主導来比較で零性を反映する。
規約：対象宇宙は任意、Small は元の dg 圏だけに要求し、K-B の核を使用しない。
使われ方：D-20。全対象商の Perf 零像と、任意の同値な小 Perf 模型への輸送。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]

lemma dgTotalQuotientModule_acyclic
    (M : RightModule R (DGQuotient.QuotientObject D Set.univ)) :
    moduleAcyclic R _ (ForgetEnrichment.of (Complex R) M) := by
  intro x
  exact DGQuotient.quotientModule_value_acyclic R D Set.univ M ⟨x.val, Set.mem_univ _⟩

lemma dgTotalQuotientPerfect_h0_isZero
    (M : PerfectDGModule R (DGQuotient.QuotientObject D Set.univ)) :
    IsZero ((toHomotopy R _).obj (ForgetEnrichment.of (Complex R) M)) := by
  let Q := DGQuotient.QuotientObject D Set.univ
  apply IsZero.of_full_of_faithful_of_isZero (perfectDGModuleToDerived R Q Set.univ)
  exact (moduleToDerived_isZero_of_acyclic R Q
    (dgTotalQuotientModule_acyclic R D M.val)).of_iso
      ((moduleToHomotopyDerivedIso R Q).app (ForgetEnrichment.of (Complex R) M.val))

lemma dgTotalQuotientPerfect_vertex_isZero
    (z : (dgModulePerfectInfinityCategory R
      (DGQuotient.QuotientObject D Set.univ)) _⦋0⦌) : IsZeroVertex z := by
  let Q := DGQuotient.QuotientObject D Set.univ
  let := dgModulePerfectInfinityCategory_isStable R Q
  let w := chosenZeroVertex (dgModulePerfectInfinityCategory R Q)
  obtain ⟨M, rfl⟩ := Simplex.vertexEquiv.symm.surjective z
  obtain ⟨N, hN⟩ := Simplex.vertexEquiv.symm.surjective w.vertex
  have he : Simplex.vertex N = w.vertex := hN
  have hz : IsZeroVertex (X := dgModulePerfectInfinityCategory R Q) (Simplex.vertex N) :=
    he.symm ▸ w.isZero
  exact hz.of_vertexIso (dgVertexIsoOfH0 R (PerfectDGModule R Q)
    ((dgTotalQuotientPerfect_h0_isZero R D N).iso
      (dgTotalQuotientPerfect_h0_isZero R D M)))

end SerrePositivity.InfinityCategories
