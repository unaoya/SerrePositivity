module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictCoherentCellEvaluation

/-!
概要：元の native 余錐セルの前面の全パラメーター関手を、元の strict 図式のセルへ戻す。
方針：既存の前面の厳密等号と、元の同じ閉零頂点成分を使う。
規約：前面の一致を対象ごとだけで述べず、全関手の厳密等号で示す。
使われ方：3b-3 R6、元の全余錐族の下方図式の一致。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
open SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison

/-- 元の native セルの前面は、元の図式の同じ全パラメーターセル関手。 -/
lemma strictBarNativeSimplexFunctor_front (A : Type u) [CommRing A]
    (J : Type) [SmallCategory J] {n : ℕ}
    (s : ((SSet.uliftFunctor.{u, 0}).obj (nerve J)) _⦋n⦌) :
    strictBarNativeSimplexFunctor A J s ⋙
        strictSimplexPullbackFunctor A (RightModule A PUnit.{1}) Fin.castSuccOrderEmb.toOrderHom =
      (strictModuleCoherentFamily A J (𝟭 (J ⥤ ModuleCategory A PUnit.{1}))).cellFunctor s := by
  apply CategoryTheory.Functor.hext
  · intro F
    exact congrArg (fun t : Simplex A (RightModule A PUnit.{1}) n =>
        (⟨t⟩ : StrictSimplexCategory A (RightModule A PUnit.{1}) n))
      (dgCoherentBarNativeSimplex_front A PUnit.{1} (smallStrictBarDiagram A F)
        (dgCoherentBarMaurerCartan_unconditional A PUnit.{1} (smallStrictBarDiagram A F)) s)
  · intro F G η
    apply StrictSimplexMap.hext
    · exact dgCoherentBarNativeSimplexData_front A PUnit.{1} (smallStrictBarDiagram A F)
        (dgCoherentBarMaurerCartan_unconditional A PUnit.{1} (smallStrictBarDiagram A F)) s
    · exact dgCoherentBarNativeSimplexData_front A PUnit.{1} (smallStrictBarDiagram A G)
        (dgCoherentBarMaurerCartan_unconditional A PUnit.{1} (smallStrictBarDiagram A G)) s
    · intro i
      exact strictBarNativeSimplexApp_castSucc_heq A J η s i

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
