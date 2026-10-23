module

public import SerrePositivity.InfinityCategories.F1.MappingSpaces.IntervalSquareRestrictionFiber
public import SerrePositivity.InfinityCategories.F1.Transport.WitnessRestrictionFiber
public import SerrePositivity.InfinityCategories.F1.Transport.WitnessRestrictionFibration
public import SerrePositivity.InfinityCategories.Core.RightFibrationContractible

/-!
概要：区間上の実際の表現空間の境界制限は trivial Kan fibration。
方針：境界表現の両端同値で周囲の fiber の可縮性を得て、全部分複体の fiber へ移す。
規約：表現の存在や分類図式の選択を追加仮定に置かない。
使われ方：Kerodon Lemma 5.6.9.1、点と単体上の表現空間の可縮性への入力。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

local instance {E : SSet.{u}} (p : E ⟶ (Δ[1] : SSet.{u})) [LeftFibration p] :
    LeftFibration (pullback.snd p (boundary 1).ι) :=
  ⟨leftFibrations.pullback_snd p (boundary 1).ι (LeftFibration.mem (p := p))⟩

/-- 概要：区間の境界は全頂点を被覆する。
方針：各頂点に境界への所属証明を添える。
規約：二つの端点をともに含む。
使われ方：表現条件の境界からの反映。 -/
lemma intervalBoundary_vertexSurjective :
    Function.Surjective ((boundary 1).ι.app (Opposite.op ⦋0⦌) :
      (boundary 1 : SSet.{u}) _⦋0⦌ → _) := by
  intro v
  obtain ⟨i, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective v
  exact ⟨intervalBoundaryVertex i, rfl⟩

/-- 概要：境界上の表現を固定した区間の周囲の四角形の制限 fiber は可縮。
方針：境界表現から実際の両端同値を取り出し、同時端点 fiber の可縮性を移す。
規約：底と全空間の二つの射をともに固定する。
使われ方：実際の表現空間の境界 fiber の可縮性。 -/
lemma intervalSquareRestrictionFiber_isContractibleKan {E : SSet.{u + 1}}
    (p : E ⟶ (Δ[1] : SSet.{u + 1})) [LeftFibration p]
    (S : LeftTransportSquare (pullback.snd p (boundary 1).ι)) (hS : S.IsRepresentation) :
    IsContractibleKan (vertexFiber (transportSquareRestriction p (boundary 1).ι)
      (transportSquareVertex S)) :=
  isContractibleKan_of_iso (intervalSquareRestrictionFiberIso p S).symm
    (intervalSquareBoundaryConstraintFiber_isContractibleKan p
      (S.intervalBoundaryFiberMap 0) (S.intervalBoundaryFiberMap_isQCatEquivalence hS 0)
      (S.intervalBoundaryFiberMap 1) (S.intervalBoundaryFiberMap_isQCatEquivalence hS 1))

/-- 概要：区間の実際の表現空間の境界制限の全 fiber は可縮。
方針：指定頂点を境界表現として回収し、周囲の fiber との厳密な同型で可縮性を戻す。
規約：任意の境界表現を厳密に固定する。
使われ方：Kerodon Lemma 5.6.9.1 の全パラメーターでの相対延長。 -/
lemma intervalWitnessRestrictionFiber_isContractibleKan {E : SSet.{u + 1}}
    (p : E ⟶ (Δ[1] : SSet.{u + 1})) [LeftFibration p]
    (v : (transportWitnessSpace (pullback.snd p (boundary 1).ι)) _⦋0⦌) :
    IsContractibleKan (vertexFiber (transportWitnessRestriction p (boundary 1).ι) v) := by
  obtain ⟨R, rfl⟩ := transportWitnessVertex_surjective _ v
  exact isContractibleKan_of_iso
    (transportWitnessRestrictionFiberIso p (boundary 1).ι intervalBoundary_vertexSurjective
      (transportWitnessVertex R)).symm
    (intervalSquareRestrictionFiber_isContractibleKan p R.toSquare R.toSquare_isRepresentation)

/-- 概要：区間の実際の表現空間の境界制限は trivial Kan fibration。
方針：既証明の全ホーン充填と各境界表現の fiber の可縮性を合わせる。
規約：モデル構造の instance を仮定せずホーンと境界の持ち上げ性だけを用いる。
使われ方：Kerodon Lemma 5.6.9.1 の空間値版。 -/
lemma intervalWitnessRestriction_trivialKanFibration {E : SSet.{u + 1}}
    (p : E ⟶ (Δ[1] : SSet.{u + 1})) [LeftFibration p] :
    TrivialKanFibration (transportWitnessRestriction p (boundary 1).ι) := by
  let q := transportWitnessRestriction p (boundary 1).ι
  have hq := (SSet.modelCategoryQuillen.fibration_iff q).mp
    (transportWitnessRestriction_fibration p (boundary 1).ι)
  let : RightFibration q := ⟨by
    intro A B i hi
    cases hi with
    | @intro n k hk => exact hq _ (SSet.modelCategoryQuillen.horn_ι_mem_J _ k)⟩
  exact rightFibration_trivialKanFibration_of_contractible_fibers q
    (intervalWitnessRestrictionFiber_isContractibleKan p)

end SerrePositivity.InfinityCategories
