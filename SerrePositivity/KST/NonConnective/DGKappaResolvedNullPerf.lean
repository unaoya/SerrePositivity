module
public import SerrePositivity.KST.NonConnective.DGKappaResolvedConnectiveSquare
public import SerrePositivity.DifferentialGraded.Quotient.DerivedComparison.LocalFlatness
public import SerrePositivity.DifferentialGraded.Derived.Basic
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Triangles.DGStableHomotopyEquivalence
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.CompactnessAndPresentability.DGPerfectModulesInfinity

/-!
概要：同じ実核の全対象商について、残っていた実零角の Perf 零性を証明する。
方針：D 正本の指定 ε による全加群の評価 acyclic 性と、Perf の完全忠実な主導来比較を使う。
規約：同じ K-B 零角に特殊化し、対象別 ε の自然性や新しい一般 dg 加群 API は仮定しない。
使われ方：K-7 c5 の一般構造射に残る零角条件の実供給。元の Perf・P 照合は別途必要。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory Limits SSet
open scoped Simplicial
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.NonConnective

variable (R : Type u) [CommRing R] (D : Type (max (u + 1) v))
  [DGCategory R D] [Small.{u} D] {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)

/-- 元の同じ全対象商上の全右加群は、指定 ε により評価ごとに acyclic。 -/
theorem dgKappaResolvedNullModule_acyclic
    (M : RightModule R (dgFixedNullInput R (dgKappaResolvedKernelKInput R D I))) :
    moduleAcyclic R (dgFixedNullInput R (dgKappaResolvedKernelKInput R D I))
      (ForgetEnrichment.of (Complex R) M) := by
  intro x
  exact DGQuotient.quotientModule_value_acyclic R (dgKappaResolvedKernelKInput R D I)
    Set.univ M ⟨x.val, Set.mem_univ x.val⟩

/-- 同じ全対象商上の実 Perf 対象は、完全忠実な主導来比較を介して H⁰ で零となる。 -/
theorem dgKappaResolvedNullPerfect_h0_isZero
    (M : PerfectDGModule R (dgFixedNullInput R (dgKappaResolvedKernelKInput R D I))) :
    IsZero ((toHomotopy R _).obj (ForgetEnrichment.of (Complex R) M)) := by
  let Q := dgFixedNullInput R (dgKappaResolvedKernelKInput R D I)
  let H := perfectDGModuleToDerived R Q Set.univ
  let X := (toHomotopy R (PerfectDGModule R Q)).obj (ForgetEnrichment.of (Complex R) M)
  have hz := moduleToDerived_isZero_of_acyclic R Q (dgKappaResolvedNullModule_acyclic R D I M.val)
  have hH : IsZero (H.obj X) := hz.of_iso
    ((moduleToHomotopyDerivedIso R Q).app (ForgetEnrichment.of (Complex R) M.val))
  exact IsZero.of_full_of_faithful_of_isZero H X hH

/-- 同じ全対象商の実 Perf nerve の全頂点は、実零頂点である。 -/
theorem dgKappaResolvedNullPerfect_vertex_isZero
    (z : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (PerfectDGModule R
      (dgFixedNullInput R (dgKappaResolvedKernelKInput R D I)))).obj (Opposite.op ⦋0⦌)) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex z := by
  let Q := dgFixedNullInput R (dgKappaResolvedKernelKInput R D I)
  let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModulePerfectInfinityCategory_isStable R Q
  let w := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.chosenZeroVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (PerfectDGModule R Q))
  obtain ⟨M, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv.symm.surjective z
  obtain ⟨N, hN⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv.symm.surjective w.vertex
  have e := (dgKappaResolvedNullPerfect_h0_isZero R D I N).iso
    (dgKappaResolvedNullPerfect_h0_isZero R D I M)
  have hn : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (PerfectDGModule R Q))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex N) := by
    have he : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex N = w.vertex := hN
    exact he.symm ▸ w.isZero
  exact hn.of_vertexIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVertexIsoOfH0 R (PerfectDGModule R Q) e)

/-- 同じ実零角の固定 ν（Perf 値）は零。P との比較や ν 上の Verdier 性は要求しない。 -/
theorem dgKappaResolvedNullPerf_isZero :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.IsZeroCategory (dgKInputStableValue R (dgFixedNullInput R (dgKappaResolvedKernelKInput R D I))) := by
  let Q := dgFixedNullInput R (dgKappaResolvedKernelKInput R D I)
  let e := presentedPerfectDGNerveEquivalence R Q
  let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModulePerfectInfinityCategory_isStable R Q
  let := presentedPerfectDGNerve_isStable R Q
  have hInv := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isExactFunctor_of_isQCatEquivalence e.symm.isQCatEquivalence
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor e.inv at hInv
  letI : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor e.inv := hInv
  intro z
  have hz := dgKappaResolvedNullPerfect_vertex_isZero R D I (e.hom.app _ z)
  have hi := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesZero (F := e.inv) _ hz
  exact hi.of_vertexIso (e.homInvIso.app z)

end SerrePositivity.KST.NonConnective
