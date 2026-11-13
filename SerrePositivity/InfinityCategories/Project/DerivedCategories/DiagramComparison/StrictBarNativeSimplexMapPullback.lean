module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictBarNativeSimplexMapAlgebra
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.NativeSimplexNaturality

/-!
概要：元の native 余錐の全 HA 写像が、面・退化による引き戻しと可換することを示す。
方針：既存の native 単体の全引き戻しの等式と、同じ閉零頂点成分を比較する。
規約：全ての単調写像を扱い、退化を除外しない。
使われ方：3b-3 R6、元の指定余錐の全パラメーター族。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
open SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable (A : Type u) [CommRing A] (J : Type) [SmallCategory J]

/-- 元の全 HA 写像は、apex を保つ元の面・退化の全引き戻しに自然である。 -/
lemma strictBarNativeSimplexMap_pullback {F G : J ⥤ ModuleCategory A PUnit.{1}}
    (η : F ⟶ G) {m n : ℕ} (s : ((SSet.uliftFunctor.{u, 0}).obj (nerve J)) _⦋n⦌)
    (α : Fin (m + 1) →o Fin (n + 1)) :
    HEq (strictBarNativeSimplexMap A J η
        (((SSet.uliftFunctor.{u, 0}).obj (nerve J)).map (SimplexCategory.mkHom α).op s))
      ((strictBarNativeSimplexMap A J η s).pullback (extendOrderHom α)) := by
  apply StrictSimplexMap.hext
  · exact dgCoherentBarNativeSimplexData_map A PUnit.{1} (smallStrictBarDiagram A F)
      (dgCoherentBarMaurerCartan_unconditional A PUnit.{1} (smallStrictBarDiagram A F)) s α
  · exact dgCoherentBarNativeSimplexData_map A PUnit.{1} (smallStrictBarDiagram A G)
      (dgCoherentBarMaurerCartan_unconditional A PUnit.{1} (smallStrictBarDiagram A G)) s α
  · intro i
    let t := ((SSet.uliftFunctor.{u, 0}).obj (nerve J)).map (SimplexCategory.mkHom α).op s
    change HEq (strictBarNativeSimplexApp A J η t i)
      (strictBarNativeSimplexApp A J η s ((extendOrderHom α) i))
    induction i using Fin.lastCases with
    | last =>
      rw [extendOrderHom_last]
      exact (strictBarNativeSimplexApp_last_heq A J η t).trans
        (strictBarNativeSimplexApp_last_heq A J η s).symm
    | cast i =>
      rw [extendOrderHom_castSucc]
      exact (strictBarNativeSimplexApp_castSucc_heq A J η t i).trans
        (strictBarNativeSimplexApp_castSucc_heq A J η s (α i)).symm

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
