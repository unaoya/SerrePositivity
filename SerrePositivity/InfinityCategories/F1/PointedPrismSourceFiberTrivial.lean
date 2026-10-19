module

public import SerrePositivity.InfinityCategories.F1.PrismSourceFiberFibration
public import SerrePositivity.InfinityCategories.Core.KanFibrationEquivalence

/-!
概要：同値な始点の fiber 上の全 pointed-space lift の終点制限は trivial Kan fibration。
方針：同時端点制限の Kan fibration 性と既証明の fiber 上の同値性を合わせる。
規約：二端点を固定した lift 空間の可縮性まで含む。
使われ方：Kerodon Lemma 5.6.9.1 の中間空間の各 fiber の可縮性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
  HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

attribute [local instance] vertexFiber_kanComplex_of_leftFibration

/-- 概要：同値な始点写像の fiber 上の終点制限は trivial Kan fibration。
方針：全ホーン充填を実際の始点 fiber へ制限し、終点同値性を使う。
規約：標準輸送への比較射ではなく実際の終点射そのものの結論。
使われ方：両端の比較を指定した lift の可縮性。 -/
lemma pointedPrismSourceFiberEndpoint_trivialKanFibration {K : SSet.{u + 1}}
    [Quasicategory K] {s : SpaceInfinity.{u} _⦋0⦌}
    (f : K ⟶ vertexFiber pointedSpaceProjection s) (hf : IsQCatEquivalence f)
    (t : SpaceInfinity.{u} _⦋0⦌) :
    TrivialKanFibration (vertexFiberι (pointedPrismLiftSource K s t) (functorVertex f) ≫
      pointedPrismLiftEndpoint K s t) := by
  let : Fibration (lift (pointedPrismLiftSource K s t) (pointedPrismLiftEndpoint K s t)) :=
    pointedPrismLiftEndpoints_fibration K s t
  let : Fibration (vertexFiberι (pointedPrismLiftSource K s t) (functorVertex f) ≫
      pointedPrismLiftEndpoint K s t) :=
    fibration_sourceVertexFiber (pointedPrismLiftSource K s t) (pointedPrismLiftEndpoint K s t) _
  exact trivialKanFibration_of_fibration_of_isQCatEquivalence _
    (pointedPrismSourceFiberEndpoint_isQCatEquivalence f hf t)

/-- 概要：同値な始点と任意の終点写像を厳密に固定した全 lift の空間は可縮。
方針：実際の終点制限の trivial Kan fibration の頂点 fiber を取る。
規約：終点写像に同値性は要求しない。
使われ方：始点同値へ制限した同時端点制限の fiber の可縮性。 -/
lemma pointedPrismFixedEndpoints_isContractibleKan {K : SSet.{u + 1}}
    [Quasicategory K] {s : SpaceInfinity.{u} _⦋0⦌}
    (f : K ⟶ vertexFiber pointedSpaceProjection s) (hf : IsQCatEquivalence f)
    (t : SpaceInfinity.{u} _⦋0⦌) (g : K ⟶ vertexFiber pointedSpaceProjection t) :
    IsContractibleKan (vertexFiber
      (vertexFiberι (pointedPrismLiftSource K s t) (functorVertex f) ≫
        pointedPrismLiftEndpoint K s t) (functorVertex g)) := by
  have := pointedPrismSourceFiberEndpoint_trivialKanFibration f hf t
  exact vertexFiber_isContractibleKan _ _

end SerrePositivity.InfinityCategories
