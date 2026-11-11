module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.WeightedCoherentCoefficients

/-!
概要：coherent な錐の始点を動かす Hom パラメータを、path の全標準単体で評価する。
方針：最初の正頂点の座標を全初区間へ含め、合成と添字変換との整合性を示す。
規約：元の錐の tail の strict 性を仮定しない。
使われ方：HTT 4.2.4.1 の錐全体上の豊穣 Hom の族の構成。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SimplicialThickening MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
noncomputable section

/-- path の最初の正頂点を、全パラメータの反転標準単体へ写す座標。 -/
def pathFirstParameterMap {n : ℕ} (j : Fin (n + 1)) :
    nerve (Path (ULift.up 0 : ULift.{u} (Fin (n + 2))) (ULift.up j.succ)) ⟶
      (Δ[n] : SSet.{u}).op :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.pathFirstMinimumMap j ≫ SSet.opFunctor.map
    (stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion j.val n (Nat.le_of_lt_succ j.isLt)))

/-- 正頂点で path を合成しても全パラメータの座標は前半の path によって決まる。 -/
lemma pathFirstParameterMap_comp {n : ℕ} (i j : Fin (n + 1)) (h : i ≤ j) :
    eComp SSet
        (⟨ULift.up 0⟩ : SimplicialThickening (ULift.{u} (Fin (n + 2))))
        ⟨ULift.up i.succ⟩ ⟨ULift.up j.succ⟩ ≫ pathFirstParameterMap j =
      CartesianMonoidalCategory.fst _ _ ≫ pathFirstParameterMap i := by
  unfold pathFirstParameterMap
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.pathFirstMinimumMap_comp i j h]
  simp only [Category.assoc]
  rw [← Functor.map_comp, ← Functor.map_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion_comp]

/-- 始点を固定する添字変換は、全パラメータの標準単体の制限と可換。 -/
lemma pathFirstParameterMap_reindex {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌) (j : Fin (m + 1)) :
    nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.pathFirstReindexFunctor α.toOrderHom j) ≫
        pathFirstParameterMap (α.toOrderHom j) =
      pathFirstParameterMap j ≫ SSet.opFunctor.map (stdSimplex.map α) := by
  unfold pathFirstParameterMap
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.pathFirstMinimumMap_reindex]
  simp only [Category.assoc]
  rw [← Functor.map_comp, ← Functor.map_comp, ← _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixRestriction_factor]
  simp only [Functor.map_comp]

/-- 豊穣合成の結合則を、任意の次数の三つの単体で評価した式。 -/
lemma simplicialHom_assoc_elements {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (W X Y Z : C) (d : SimplexCategoryᵒᵖ)
    (a : (SimplicialCategory.sHom W X).obj d)
    (b : (SimplicialCategory.sHom X Y).obj d)
    (c : (SimplicialCategory.sHom Y Z).obj d) :
    (eComp SSet W Y Z).app d ((eComp SSet W X Y).app d (a, b), c) =
      (eComp SSet W X Z).app d (a, (eComp SSet X Y Z).app d (b, c)) := by
  exact congrArg (fun f : SimplicialCategory.sHom W X ⊗
      (SimplicialCategory.sHom X Y ⊗ SimplicialCategory.sHom Y Z) ⟶
        SimplicialCategory.sHom W Z ↦ f.app d (a, (b, c))) (e_assoc SSet W X Y Z)

end
end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
