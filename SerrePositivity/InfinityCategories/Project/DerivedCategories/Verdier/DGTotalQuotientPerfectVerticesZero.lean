module
public import SerrePositivity.DifferentialGraded.Quotient.DerivedComparison.LocalFlatness
public import SerrePositivity.DifferentialGraded.Derived.Basic
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Triangles.DGStableHomotopyEquivalence
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.CompactnessAndPresentability.DGPerfectModulesInfinity
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded SSet
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]

lemma dgTotalQuotientModule_acyclic
    (M : _root_.SerrePositivity.DifferentialGraded.RightModule R (_root_.SerrePositivity.DifferentialGraded.DGQuotient.QuotientObject D Set.univ)) :
    _root_.SerrePositivity.DifferentialGraded.moduleAcyclic R _ (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) M) := by
  intro x
  exact _root_.SerrePositivity.DifferentialGraded.DGQuotient.quotientModule_value_acyclic R D Set.univ M ⟨x.val, Set.mem_univ _⟩

lemma dgTotalQuotientPerfect_h0_isZero
    (M : _root_.SerrePositivity.DifferentialGraded.PerfectDGModule R (_root_.SerrePositivity.DifferentialGraded.DGQuotient.QuotientObject D Set.univ)) :
    IsZero ((_root_.SerrePositivity.DifferentialGraded.toHomotopy R _).obj (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) M)) := by
  let Q := _root_.SerrePositivity.DifferentialGraded.DGQuotient.QuotientObject D Set.univ
  apply IsZero.of_full_of_faithful_of_isZero (_root_.SerrePositivity.DifferentialGraded.perfectDGModuleToDerived R Q Set.univ)
  exact (_root_.SerrePositivity.DifferentialGraded.moduleToDerived_isZero_of_acyclic R Q
    (dgTotalQuotientModule_acyclic R D M.val)).of_iso
      ((_root_.SerrePositivity.DifferentialGraded.moduleToHomotopyDerivedIso R Q).app (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) M.val))

lemma dgTotalQuotientPerfect_vertex_isZero
    (z : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModulePerfectInfinityCategory R
      (DGQuotient.QuotientObject D Set.univ)) _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex z := by
  let Q := _root_.SerrePositivity.DifferentialGraded.DGQuotient.QuotientObject D Set.univ
  let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModulePerfectInfinityCategory_isStable R Q
  let w := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.chosenZeroVertex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModulePerfectInfinityCategory R Q)
  obtain ⟨M, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv.symm.surjective z
  obtain ⟨N, hN⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv.symm.surjective w.vertex
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex N = w.vertex := hN
  have hz : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (X := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModulePerfectInfinityCategory R Q) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex N) :=
    he.symm ▸ w.isZero
  exact hz.of_vertexIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVertexIsoOfH0 R (PerfectDGModule R Q)
    ((dgTotalQuotientPerfect_h0_isZero R D N).iso
      (dgTotalQuotientPerfect_h0_isZero R D M)))

end SerrePositivity.InfinityCategories.Project.DerivedCategories
