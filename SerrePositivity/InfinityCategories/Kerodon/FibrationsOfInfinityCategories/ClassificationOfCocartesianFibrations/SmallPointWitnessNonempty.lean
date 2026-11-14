module


public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.PointWitnessContractibilityCriterion
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.NerveTransportRepresentation
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.UniverseSSetMaps

/-!
概要：小さい Kan 複体の宇宙持ち上げの点上の表現空間は非空。
方針：通常の点の nerve 上の実際の表現を取り、底を標準点へ同型で戻す。
規約：表現の存在を追加仮定に置かない。
使われ方：Kerodon Lemma 5.6.9.2（Tag 02SR） の小さい全空間の非空性。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：小さい Kan 複体を一段持ち上げた全空間の点上の表現空間は非空。
方針：通常の点の nerve 上の既存の表現を底の同型で標準点へ移す。
規約：全空間の小ささから実際の表現を構成する。
使われ方：点上の表現空間の可縮性の主経路の非空性。 -/
lemma smallPointWitnessSpace_nonempty (E : SSet.{u}) [KanComplex E] :
    Nonempty ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessSpace
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportPointProjection ((SSet.uliftFunctor.{u + 1, u}).obj E))) _⦋0⦌) := by
  let U := SSet.uliftFunctor.{u + 1, u}
  let p := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportPointProjection E
  let e := stdSimplex.isoNerve.{u} 0
  let q := p ≫ e.hom
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration q := ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrations.comp_mem _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration.mem (p := p))
    (MorphismProperty.rlp_of_isIso _ _)⟩
  let R := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.nerveLeftTransportRepresentation q
  let d := (U.mapIso e).symm ≪≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftStdSimplexIso.{u, u + 1} 0
  let q' := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportPointProjection (U.obj E)
  have hq : U.map q ≫ d.hom = q' := stdSimplex.isTerminalObj₀.hom_ext _ _
  let h := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportWitnessBaseIsoOfComm (U.map q) q' d hq
  exact ⟨h.inv.app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessVertex R)⟩

/-- 概要：小さい Kan 複体の宇宙持ち上げの点上の表現空間は可縮 Kan。
方針：実際に構成した非空性と区間境界制限による可縮性判定を合わせる。
規約：表現の存在仮定を主経路に置かない。
使われ方：Kerodon Lemma 5.6.9.2（Tag 02SR） の小さい全空間版。 -/
lemma smallPointWitnessSpace_isContractibleKan (E : SSet.{u}) [KanComplex E] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessSpace
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportPointProjection ((SSet.uliftFunctor.{u + 1, u}).obj E))) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointWitnessSpace_isContractibleKan_of_nonempty _ (smallPointWitnessSpace_nonempty E)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
