module

public import SerrePositivity.InfinityCategories.F1.RelativeHomPointedShortEdges
public import SerrePositivity.InfinityCategories.F1.DiagonalFiberTransportSourceIso

/-!
概要：同じ pointed 自然性の四角形の終点を、二つの順序の実際の普遍輸送で比較する。
方針：残る二辺で動く始点の対角輸送を使い、四角形の同じ終点を経由して比較する。
規約：射と変換のパラメーターを同時に保つ。全標的での往復の恒等性は別工程。
使われ方：回収と主比較の反対向きの合成の自然性の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 終域の Hom 関手の作用を被覆する、自然性の最後の横辺。 -/
def relativeHomPointedFinalRowPrism {B : SSet.{u}} (a q r : LeftFibrationObject B) :=
  prismEndpoint 1 _ ≫ relativeHomCoherentNaturalitySquare a q r

/-- 最後の横辺の始点は、表現対象での終域の Hom 関手の値。 -/
lemma relativeHomPointedFinalRowPrism_zero {B : SSet.{u}} (a q r : LeftFibrationObject B) :
    prismEndpoint 0 _ ≫ relativeHomPointedFinalRowPrism a q r =
      SSet.const ((leftFibrationCoherentEvaluation a.val).app (Opposite.op ⦋0⦌)
        (coherentNerveVertex q)) := by
  rw [relativeHomPointedFinalRowPrism,
    relativeHomCoherentNaturalitySquare_transformation_one,
    ← Category.assoc, prismEndpoint_naturality, Category.assoc]
  rw [← Category.assoc (prismEndpoint 0 _) (relativeHomArrowPrism q r)
    (leftFibrationCoherentEvaluation a.val), relativeHomArrowPrism_zero q r,
    SSet.const_comp, SSet.comp_const]

/-- 最後の横辺の終点は、各標的での終域の Hom 関手の値。 -/
lemma relativeHomPointedFinalRowPrism_one {B : SSet.{u}} (a q r : LeftFibrationObject B) :
    prismEndpoint 1 _ ≫ relativeHomPointedFinalRowPrism a q r =
      SSet.const ((leftFibrationCoherentEvaluation a.val).app (Opposite.op ⦋0⦌)
        (coherentNerveVertex r)) := by
  rw [relativeHomPointedFinalRowPrism,
    relativeHomCoherentNaturalitySquare_transformation_one,
    ← Category.assoc, prismEndpoint_naturality, Category.assoc]
  rw [← Category.assoc (prismEndpoint 1 _) (relativeHomArrowPrism q r)
    (leftFibrationCoherentEvaluation a.val), relativeHomArrowPrism_one q r,
    SSet.const_comp, SSet.comp_const]

/-- 各標的での coherent 変換の評価を被覆する、最後の縦辺。 -/
def relativeHomPointedTargetPrism {B : SSet.{u}} (a q r : LeftFibrationObject B) :=
  (Δ[1] ◁ prismEndpoint 1 _) ≫ relativeHomCoherentNaturalitySquare a q r

/-- 最後の縦辺は、最初の横辺の終点から始まる。 -/
lemma relativeHomPointedTargetPrism_zero {B : SSet.{u}} (a q r : LeftFibrationObject B) :
    prismEndpoint 0 _ ≫ relativeHomPointedTargetPrism a q r =
      SSet.const ((leftFibrationCoherentEvaluation q.val).app (Opposite.op ⦋0⦌)
        (coherentNerveVertex r)) := by
  rw [relativeHomPointedTargetPrism, ← Category.assoc, prismEndpoint_square_exchange,
    Category.assoc]
  exact relativeHomPointedInitialRowPrism_one a q r

/-- 最後の縦辺と最後の横辺は、同じ fiber で終わる。 -/
lemma relativeHomPointedTargetPrism_one {B : SSet.{u}} (a q r : LeftFibrationObject B) :
    prismEndpoint 1 _ ≫ relativeHomPointedTargetPrism a q r =
      SSet.const ((leftFibrationCoherentEvaluation a.val).app (Opposite.op ⦋0⦌)
        (coherentNerveVertex r)) := by
  rw [relativeHomPointedTargetPrism, ← Category.assoc, prismEndpoint_square_exchange,
    Category.assoc]
  exact relativeHomPointedFinalRowPrism_one a q r

/-- 同じ pointed 四角形の終点を、実際の終点 fiber 内の射として表す。 -/
def relativeHomPointedSquareEndpoint {B : SSet.{u}} (a q r : LeftFibrationObject B)
    (W : _ ⟶ PointedSpaceInfinity.{u})
    (hW : W ≫ pointedSpaceProjection = relativeHomCoherentNaturalitySquare a q r) :
    (SSet.uliftFunctor.{u + 1, u}).obj (relativeFunctorSpace r.val.hom q.val.hom) ⊗
      pinchedHom (functorVertex (leftFibrationCoherentEvaluation q.val))
        (functorVertex (leftFibrationCoherentEvaluation a.val)) ⟶
    vertexFiber pointedSpaceProjection
      ((leftFibrationCoherentEvaluation a.val).app (Opposite.op ⦋0⦌) (coherentNerveVertex r)) :=
  vertexFiberLift _ _ (prismEndpoint 1 _ ≫ prismEndpoint 1 _ ≫ W) (by
    rw [Category.assoc, Category.assoc, hW]
    exact relativeHomPointedFinalRowPrism_one a q r)

/-- 変換を先に作用させる順序の最後の辺は、動く始点の実際の対角輸送。 -/
def relativeHomPointedFinalRowEndpoint_transportIso {B : SSet.{u}}
    (a q r : LeftFibrationObject B) (W : _ ⟶ PointedSpaceInfinity.{u})
    (hW : W ≫ pointedSpaceProjection = relativeHomCoherentNaturalitySquare a q r) :
    FunctorIso (relativeHomPointedSquareEndpoint a q r W hW)
      (diagonalFiberTransport pointedSpaceProjection (relativeHomPointedSourceEndpoint a q r W hW)
        (intervalMappingCurryOfEndpoints (relativeHomPointedFinalRowPrism a q r)
          (relativeHomPointedFinalRowPrism_zero a q r)
          (relativeHomPointedFinalRowPrism_one a q r))) := by
  apply leftFibrationPrism_diagonalTransportIso pointedSpaceProjection
    (relativeHomPointedSourceEndpoint a q r W hW) (relativeHomPointedSquareEndpoint a q r W hW)
    (relativeHomPointedFinalRowPrism a q r) (relativeHomPointedFinalRowPrism_zero a q r)
    (relativeHomPointedFinalRowPrism_one a q r) (prismEndpoint 1 _ ≫ W)
  · rw [← Category.assoc, ← prismEndpoint_square_exchange, Category.assoc]
    exact (vertexFiberLift_ι _ _ _ _).symm
  · exact (vertexFiberLift_ι _ _ _ _).symm
  · rw [Category.assoc, hW]
    rfl

/-- 元の Hom の射を先に作用させる順序の最後の辺も、同じ対角輸送で比較できる。 -/
def relativeHomPointedTargetEndpoint_transportIso {B : SSet.{u}}
    (a q r : LeftFibrationObject B) (W : _ ⟶ PointedSpaceInfinity.{u})
    (hW : W ≫ pointedSpaceProjection = relativeHomCoherentNaturalitySquare a q r) :
    FunctorIso (relativeHomPointedSquareEndpoint a q r W hW)
      (diagonalFiberTransport pointedSpaceProjection
        (relativeHomPointedInitialRowEndpoint a q r W hW)
        (intervalMappingCurryOfEndpoints (relativeHomPointedTargetPrism a q r)
          (relativeHomPointedTargetPrism_zero a q r)
          (relativeHomPointedTargetPrism_one a q r))) := by
  apply leftFibrationPrism_diagonalTransportIso pointedSpaceProjection
    (relativeHomPointedInitialRowEndpoint a q r W hW)
    (relativeHomPointedSquareEndpoint a q r W hW)
    (relativeHomPointedTargetPrism a q r) (relativeHomPointedTargetPrism_zero a q r)
    (relativeHomPointedTargetPrism_one a q r) ((Δ[1] ◁ prismEndpoint 1 _) ≫ W)
  · rw [← Category.assoc, prismEndpoint_square_exchange, Category.assoc]
    exact (vertexFiberLift_ι _ _ _ _).symm
  · rw [← Category.assoc, prismEndpoint_square_exchange, Category.assoc]
    exact (vertexFiberLift_ι _ _ _ _).symm
  · rw [Category.assoc, hW]
    rfl

/-- 二つの合成順序の普遍輸送の評価は、同じ pointed 四角形の終点を介して関手同型。 -/
def relativeHomPointedTransportSquareIso {B : SSet.{u}}
    (a q r : LeftFibrationObject B) (W : _ ⟶ PointedSpaceInfinity.{u})
    (hW : W ≫ pointedSpaceProjection = relativeHomCoherentNaturalitySquare a q r) :
    FunctorIso
      (diagonalFiberTransport pointedSpaceProjection
        (relativeHomPointedInitialRowEndpoint a q r W hW)
        (intervalMappingCurryOfEndpoints (relativeHomPointedTargetPrism a q r)
          (relativeHomPointedTargetPrism_zero a q r) (relativeHomPointedTargetPrism_one a q r)))
      (diagonalFiberTransport pointedSpaceProjection (relativeHomPointedSourceEndpoint a q r W hW)
        (intervalMappingCurryOfEndpoints (relativeHomPointedFinalRowPrism a q r)
          (relativeHomPointedFinalRowPrism_zero a q r)
          (relativeHomPointedFinalRowPrism_one a q r))) :=
  (relativeHomPointedTargetEndpoint_transportIso a q r W hW).symm ≪≫
    relativeHomPointedFinalRowEndpoint_transportIso a q r W hW

/-- 元の Hom の射を先に、coherent な変換を後に作用させる標準の二段輸送。 -/
def relativeHomPointedArrowThenTransformation {B : SSet.{u}} (a q r : LeftFibrationObject B) :=
  diagonalFiberTransport pointedSpaceProjection
    (diagonalFiberTransport pointedSpaceProjection (SSet.const (relativeHomPointedIdentity q))
      (intervalMappingCurryOfEndpoints (relativeHomPointedInitialRowPrism a q r)
        (relativeHomPointedInitialRowPrism_zero a q r)
        (relativeHomPointedInitialRowPrism_one a q r)))
    (intervalMappingCurryOfEndpoints (relativeHomPointedTargetPrism a q r)
      (relativeHomPointedTargetPrism_zero a q r) (relativeHomPointedTargetPrism_one a q r))

/-- 表現対象で変換を先に評価し、終域の Hom の射を後に作用させる標準の二段輸送。 -/
def relativeHomPointedTransformationThenArrow {B : SSet.{u}} (a q r : LeftFibrationObject B) :=
  diagonalFiberTransport pointedSpaceProjection
    (diagonalFiberTransport pointedSpaceProjection (SSet.const (relativeHomPointedIdentity q))
      (intervalMappingCurryOfEndpoints (relativeHomPointedSourcePrism a q r)
        (relativeHomPointedSourcePrism_zero a q r) (relativeHomPointedSourcePrism_one a q r)))
    (intervalMappingCurryOfEndpoints (relativeHomPointedFinalRowPrism a q r)
      (relativeHomPointedFinalRowPrism_zero a q r) (relativeHomPointedFinalRowPrism_one a q r))

/-- 任意の coherent 変換と全相対射の両パラメーターで、標準の二つの輸送順序は関手同型。 -/
def relativeHomPointedCanonicalTransportSquareIso {B : SSet.{u}}
    (a q r : LeftFibrationObject B) :
    FunctorIso (relativeHomPointedArrowThenTransformation a q r)
      (relativeHomPointedTransformationThenArrow a q r) := by
  let h := exists_relativeHomPointedNaturalitySquare a q r
  let W := h.choose
  have h₀ := h.choose_spec.1
  have hp := h.choose_spec.2
  have e₀ := diagonalFiberTransport_sourceIso pointedSpaceProjection
    (relativeHomPointedInitialRowEndpoint_transportIso a q r W hp h₀)
    (intervalMappingCurryOfEndpoints (relativeHomPointedTargetPrism a q r)
      (relativeHomPointedTargetPrism_zero a q r) (relativeHomPointedTargetPrism_one a q r))
  have e₁ := diagonalFiberTransport_sourceIso pointedSpaceProjection
    (relativeHomPointedSourceEndpoint_transportIso a q r W hp h₀)
    (intervalMappingCurryOfEndpoints (relativeHomPointedFinalRowPrism a q r)
      (relativeHomPointedFinalRowPrism_zero a q r) (relativeHomPointedFinalRowPrism_one a q r))
  exact e₀.symm ≪≫ relativeHomPointedTransportSquareIso a q r W hp ≪≫ e₁

end SerrePositivity.InfinityCategories
