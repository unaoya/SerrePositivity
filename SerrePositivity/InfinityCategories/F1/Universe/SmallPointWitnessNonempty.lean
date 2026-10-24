module

public import SerrePositivity.InfinityCategories.HomotopyLimits.WeightedConeSectionEquivalence

public import SerrePositivity.InfinityCategories.F1.Transport.PointWitnessContractibilityCriterion
public import SerrePositivity.InfinityCategories.F1.Transport.NerveTransportRepresentation
public import SerrePositivity.InfinityCategories.Core.UniverseSSetMaps

/-!
概要：小さい Kan 複体の宇宙持ち上げの点上の表現空間は非空。
方針：通常の点の nerve 上の実際の表現を取り、底を標準点へ同型で戻す。
規約：表現の存在を追加仮定に置かない。
使われ方：Kerodon Lemma 5.6.9.2 の小さい全空間の非空性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：小さい Kan 複体を一段持ち上げた全空間の点上の表現空間は非空。
方針：通常の点の nerve 上の既存の表現を底の同型で標準点へ移す。
規約：全空間の小ささから実際の表現を構成する。
使われ方：点上の表現空間の可縮性の主経路の非空性。 -/
lemma smallPointWitnessSpace_nonempty (E : SSet.{u}) [KanComplex E] :
    Nonempty ((transportWitnessSpace
      (transportPointProjection ((SSet.uliftFunctor.{u + 1, u}).obj E))) _⦋0⦌) := by
  let U := SSet.uliftFunctor.{u + 1, u}
  let p := transportPointProjection E
  let e := stdSimplex.isoNerve.{u} 0
  let q := p ≫ e.hom
  have : LeftFibration q := ⟨leftFibrations.comp_mem _ _ (LeftFibration.mem (p := p))
    (MorphismProperty.rlp_of_isIso _ _)⟩
  let R := nerveLeftTransportRepresentation q
  let d := (U.mapIso e).symm ≪≫ HomotopyLimits.uliftStdSimplexIso.{u, u + 1} 0
  let q' := transportPointProjection (U.obj E)
  have hq : U.map q ≫ d.hom = q' := stdSimplex.isTerminalObj₀.hom_ext _ _
  let h := transportWitnessBaseIsoOfComm (U.map q) q' d hq
  exact ⟨h.inv.app _ (transportWitnessVertex R)⟩

/-- 概要：小さい Kan 複体の宇宙持ち上げの点上の表現空間は可縮 Kan。
方針：実際に構成した非空性と区間境界制限による可縮性判定を合わせる。
規約：表現の存在仮定を主経路に置かない。
使われ方：Kerodon Lemma 5.6.9.2 の小さい全空間版。 -/
lemma smallPointWitnessSpace_isContractibleKan (E : SSet.{u}) [KanComplex E] :
    IsContractibleKan (transportWitnessSpace
      (transportPointProjection ((SSet.uliftFunctor.{u + 1, u}).obj E))) :=
  pointWitnessSpace_isContractibleKan_of_nonempty _ (smallPointWitnessSpace_nonempty E)

end SerrePositivity.InfinityCategories
