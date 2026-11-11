module
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoconeMappingSpace
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroHomotopy

/-! # 零枝の終点固定余錐の可縮性

概要：始対象へ向かう辺からの終点固定余錐の空間は可縮である。
方針：辺の終点への制限が自明 Kan fibration であり、始対象からの写像空間が可縮なことを使う。
規約：安定性は不要。使われ方：二枝の余錐空間をループ空間へ比較する際の可縮な因子。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：自明 Kan fibration の終域が可縮なら始域も可縮である。
方針：終域で境界を充填してから、自明 fibration で元へ持ち上げる。
規約：quasicategory 性を仮定しない。使われ方：余錐空間の可縮性の輸送。 -/
lemma stable_isContractibleKan_of_trivialKanFibration {E B : SSet.{u}}
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration p] (hB : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan B) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan E := by
  intro n b
  obtain ⟨F, hF⟩ := hB n (b ≫ p)
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem (p := p) (boundary n).ι inferInstance
  have sq : CommSq b (boundary n).ι p F := ⟨hF.symm⟩
  exact ⟨sq.lift, sq.fac_left⟩

/-- 概要：始対象から指定終点への余錐の空間は可縮。
方針：始対象の coslice 射影の自明 Kan fibration 性を頂点 fiber に移す。
規約：元の単体集合の quasicategory 性は不要。使われ方：零枝の可縮な比較空間。 -/
lemma coconeMappingSpace_point_isContractibleKan {X : SSet.{u}} {z : X _⦋0⦌}
    (hz : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex z) (y : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace (SSet.yonedaEquiv.symm z) y) := by
  have := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.isInitialVertex_iff_trivialKanFibration z).1 hz
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_isContractibleKan (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm z)) y

/-- 概要：辺の終点が始対象なら、その辺から指定終点への余錐の空間は可縮。
方針：辺の終点への制限の自明性で、始対象からの余錐の空間の可縮性を戻す。
規約：値域は quasicategory。使われ方：HA Lemma 1.1.2.10 の D(f) の可縮性。 -/
lemma coconeMappingSpace_edge_isContractibleKan {X : SSet.{u}} [Quasicategory X]
    (f : (Δ[1] : SSet.{u}) ⟶ X)
    (hz : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex (SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 2) ≫ f)))
    (y : X _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace f y) := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cosliceTriangleTarget_trivialKanFibration f y
  apply stable_isContractibleKan_of_trivialKanFibration
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cosliceRestrictionFiberMap f (stdSimplex.δ (0 : Fin 2)) y)
  have h := coconeMappingSpace_point_isContractibleKan hz y
  exact (congrArg (fun q => _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace q y))
    (SSet.yonedaEquiv.symm_apply_apply (stdSimplex.δ (0 : Fin 2) ≫ f))).mp h

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
