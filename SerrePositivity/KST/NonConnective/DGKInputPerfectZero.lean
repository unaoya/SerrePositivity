module
public import SerrePositivity.KST.NonConnective.DGKInputDerivedCompactGeneration
public import SerrePositivity.KST.SConstruction.DGKFixedInterface
public import SerrePositivity.InfinityCategories.Derived.DGStableHomotopyEquivalence
public import SerrePositivity.InfinityCategories.Stable.ZeroHomotopy
public import SerrePositivity.KST.LocalizingInvariants.VerdierDiagrams
public import SerrePositivity.InfinityCategories.Derived.DGPerfectModulesInfinity

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
  (hA : IsZeroCategory (dgKInputStableValue R A))
include hA

/-- 同じ固定 ν が零なら、元の実 Perf の全頂点も零。 -/
theorem dgKInputPerfect_vertex_isZero (z : (dgNerve R (PerfectDGModule R A)) _⦋0⦌) :
    IsZeroVertex z := by
  let e := presentedPerfectDGQCatEvaluationEquivalence R A
  let := dgModulePerfectInfinityCategory_isStable R A
  let := isExactFunctor_of_isQCatEquivalence e.isQCatEquivalence
  have hz := IsExactFunctor.preservesZero (F := e.hom) _ (hA (e.inv.app _ z))
  exact hz.of_vertexIso (e.invHomIso.app z)

/-- 同じ実 Perf 対象の H⁰ 像は零。 -/
theorem dgKInputPerfect_h0_isZero (M : PerfectDGModule R A) :
    IsZero ((toHomotopy R (PerfectDGModule R A)).obj
      (ForgetEnrichment.of (Complex R) M)) := by
  let := dgModulePerfectInfinityCategory_isStable R A
  have h := (dgStableHomotopyEquivalence R (PerfectDGModule R A)).functor.map_isZero
    (dgKInputPerfect_vertex_isZero R A hA (DGNerve.Simplex.vertex M)).isZeroHo
  simpa only [dgStableHomotopyEquivalence_obj_vertex] using h

/-- 固定 ν が零なら元の主 Perf の全対象が零。 -/
theorem dgKInputClassicalPerfect_isZero (X : PerfectModuleCategory R A) : IsZero X := by
  let H := perfectDGModuleToPerfect R A Set.univ
  obtain ⟨Y, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage H X
  have hY : IsZero Y := dgKInputPerfect_h0_isZero R A hA
    (ForgetEnrichment.to (Complex R) Y.as)
  exact (H.map_isZero hY).of_iso e.symm

end SerrePositivity.KST.NonConnective
