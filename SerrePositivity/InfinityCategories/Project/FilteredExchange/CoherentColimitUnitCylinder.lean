module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.Cocone
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.CoconeTransformationVertex
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoconeHomotopyUnitCylinder
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.CoherentColimitCoconeEdge
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.CoherentColimitCoconeHomotopy
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.CoherentColimitFunctor
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.CoherentTotalCocone
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.CoherentTotalObject

/-!
概要：元の coherent 変換に沿う、元の native 全空間余錐の単位の自然性円柱。
方針：全余錐円柱の二時間の制限を読み、底と余極限の指定辺を回収する。
規約：元の変換・両単位・頂点の辺を保持。使われ方：a6 の native 二脚との比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange
variable (B : SSet.{u})
  {F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}} (H : SSet.Homotopy F G)

/-- 元の native 全空間余錐の単位を結ぶ、元の変換に沿った二時間の円柱。 -/
def coherentColimitUnitCylinder :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeHomotopyUnitCylinder (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalCocone F) (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalCocone G)
    (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentColimitCoconeHomotopy B H)

/-- 図式側では元の指定変換の全円柱を厳密に回収する。 -/
lemma coherentColimitUnitCylinder_source :
    (SSet.ι₀ (X := (SSet.uliftFunctor.{u + 1, u}).obj B) ▷ (Δ[1] : SSet.{u + 1})) ≫
      (coherentColimitUnitCylinder B H).h = H.h := by
  rw [coherentColimitUnitCylinder, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeHomotopyUnitCylinder_source,
    _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentColimitCoconeHomotopy_restrict]

/-- 頂点側では元の余極限関手が送る指定辺を、底に関して定値な全円柱として回収する。 -/
lemma coherentColimitUnitCylinder_target :
    (SSet.ι₁ (X := (SSet.uliftFunctor.{u + 1, u}).obj B) ▷ (Δ[1] : SSet.{u + 1})) ≫
      (coherentColimitUnitCylinder B H).h =
        snd ((SSet.uliftFunctor.{u + 1, u}).obj B) Δ[1] ≫
          SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentColimitFunctorEdge B H).edge := by
  rw [coherentColimitUnitCylinder, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeHomotopyUnitCylinder_target,
    _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentColimitCoconeHomotopy_h]
  change _ = _ ≫ SSet.yonedaEquiv.symm ((_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentColimitFunctor B).app (Opposite.op ⦋1⦌)
    (SSet.yonedaEquiv (curry H.h)))
  rw [← SSet.yonedaEquiv_comp, Equiv.symm_apply_apply]
  change _ = _ ≫ (curry H.h ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentColimitCoconeFunctor B) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt _
  rfl

end SerrePositivity.InfinityCategories.Project.FilteredExchange
