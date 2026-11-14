module
public import SerrePositivity.KST.NonConnective.DGKInputDerivedCompactGeneration
public import SerrePositivity.KST.SConstruction.DGKFixedInterface
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Triangles.DGStableHomotopyEquivalence
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.ZeroHomotopy
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagrams
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.CompactnessAndPresentability.DGPerfectModulesInfinity

/-!
概要：固定 ν の零性を同じ実 Perf と主 Perf の零性へ渡す。
方針：元のラベル評価同値、h/H⁰ 比較と主 Perf 評価を使う。
規約：固定 ν と実入力を変更しない。
使われ方：K-7 f の零対象保存に必要な主導来零性の生成元。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory Limits SSet
open scoped Simplicial
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.NonConnective
variable (R : Type u) [CommRing R] (A : PerfDGInput.{u, max (u + 1) v} R)
  (hA : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.IsZeroCategory (dgKInputStableValue R A))
include hA

/-- 同じ固定 ν が零なら、元の実 Perf の全頂点も零。 -/
theorem dgKInputPerfect_vertex_isZero (z : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (PerfectDGModule R A)) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex z := by
  let e := presentedPerfectDGQCatEvaluationEquivalence R A
  let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModulePerfectInfinityCategory_isStable R A
  let := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isExactFunctor_of_isQCatEquivalence e.isQCatEquivalence
  have hz := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesZero (F := e.hom) _ (hA (e.inv.app _ z))
  exact hz.of_vertexIso (e.invHomIso.app z)

/-- 同じ実 Perf 対象の H⁰ 像は零。 -/
theorem dgKInputPerfect_h0_isZero (M : PerfectDGModule R A) :
    IsZero ((toHomotopy R (PerfectDGModule R A)).obj
      (ForgetEnrichment.of (Complex R) M)) := by
  let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModulePerfectInfinityCategory_isStable R A
  have h := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStableHomotopyEquivalence R (PerfectDGModule R A)).functor.map_isZero
    (dgKInputPerfect_vertex_isZero R A hA (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex M)).isZeroHo
  simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStableHomotopyEquivalence_obj_vertex] using h

/-- 固定 ν が零なら元の主 Perf の全対象が零。 -/
theorem dgKInputClassicalPerfect_isZero (X : PerfectModuleCategory R A) : IsZero X := by
  let H := perfectDGModuleToPerfect R A Set.univ
  obtain ⟨Y, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage H X
  have hY : IsZero Y := dgKInputPerfect_h0_isZero R A hA
    (ForgetEnrichment.to (Complex R) Y.as)
  exact (H.map_isZero hY).of_iso e.symm

end SerrePositivity.KST.NonConnective
