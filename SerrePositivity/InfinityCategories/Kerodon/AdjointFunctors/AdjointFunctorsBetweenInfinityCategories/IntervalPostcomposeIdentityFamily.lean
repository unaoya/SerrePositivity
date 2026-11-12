module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.IntervalConstantFamily

/-!
概要：恒等辺の定値全族を同じ指定辺で後合成すると、その辺の定値全族にホモトピック。
方針：全族の合成則と定値関手の恒等則を、区間族の忠実性で戻す。
規約：パラメータは任意。使われ方：G8 の錐の全 Hom 作用の恒等射での評価。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories

/-- 概要：指定辺による標準後合成は、恒等辺の定値全族を同じ辺の定値全族へ送る。
方針：全族の合成則と定値関手の恒等則から、元の全族のホモトピーを得る。
規約：点ごとの比較ではない。使われ方：元の錐の辺の値の作用の回収。 -/
lemma intervalPostcompose_identityFamily_homotopy {A X : SSet.{u}} [Quasicategory X]
    {x y : X _⦋0⦌} (e : X.Edge x y) :
    Nonempty (SSet.Homotopy
      ((SSet.const (intervalMappingVertexOfEdge (SSet.Edge.id x)) : A ⟶ _) ≫
        intervalPostcompose x (SSet.Truncated.HomotopyCategory.homMk e))
      (SSet.const (intervalMappingVertexOfEdge e))) := by
  apply intervalFamilyHom_eq_imp_homotopy
  rw [intervalPostcompose_family, intervalFamilyHom_const_edge, intervalFamilyHom_const_edge]
  have hi : SSet.Truncated.HomotopyCategory.homMk (SSet.Edge.id x).toTruncated =
      𝟙 (HomotopyCategory.mk x) := SSet.Truncated.HomotopyCategory.homMk_id _
  erw [hi, constantFunctorHomMap_id, Category.id_comp]

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories
