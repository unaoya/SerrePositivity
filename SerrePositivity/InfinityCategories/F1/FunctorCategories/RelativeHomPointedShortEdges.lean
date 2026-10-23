module

public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeHomPointedNaturality
public import SerrePositivity.InfinityCategories.F1.Transport.DiagonalFiberTransport

/-!
概要：pointed 自然性の始点側の短辺を、実際の普遍 transport の評価と比較する。
方針：四角形を表現対象の辺へ制限し、恒等射固定の始点と全パラメーターの終点を取る。
規約：変換のパラメーターを頂点へ落とさず、元の pointed 四角形の同じ短辺を使う。
使われ方：恒等射での回収を元の coherent 変換へ戻す往復の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 二つの区間の端点を補う順序は、座標を保てば厳密に可換。 -/
lemma prismEndpoint_square_exchange (i j : Fin 2) (P : SSet.{u}) :
    prismEndpoint i P ≫ (Δ[1] ◁ prismEndpoint j P) =
      prismEndpoint j P ≫ prismEndpoint i (Δ[1] ⊗ P) := rfl

/-- 表現対象での変換評価を被覆する、自然性の始点側の辺の族。 -/
def relativeHomPointedSourcePrism {B : SSet.{u}} (a q r : LeftFibrationObject B) :=
  (Δ[1] ◁ prismEndpoint 0 _) ≫ relativeHomCoherentNaturalitySquare a q r

/-- 始点側の辺は自己 Hom の空間から始まる。 -/
lemma relativeHomPointedSourcePrism_zero {B : SSet.{u}} (a q r : LeftFibrationObject B) :
    prismEndpoint 0 _ ≫ relativeHomPointedSourcePrism a q r =
      SSet.const (spaceInfinityVertex (relativeHomIdentityKanObject q)) := by
  rw [relativeHomPointedSourcePrism, ← Category.assoc, prismEndpoint_square_exchange,
    Category.assoc]
  exact relativeHomCoherentNaturalitySquare_origin a q r

/-- 始点側の辺の終点は、表現対象で評価した終域の Hom 関手。 -/
lemma relativeHomPointedSourcePrism_one {B : SSet.{u}} (a q r : LeftFibrationObject B) :
    prismEndpoint 1 _ ≫ relativeHomPointedSourcePrism a q r =
      SSet.const ((leftFibrationCoherentEvaluation a.val).app (Opposite.op ⦋0⦌)
        (coherentNerveVertex q)) := by
  rw [relativeHomPointedSourcePrism, ← Category.assoc, prismEndpoint_square_exchange,
    Category.assoc, relativeHomCoherentNaturalitySquare_transformation_one,
    ← Category.assoc, prismEndpoint_naturality, Category.assoc]
  rw [← Category.assoc (prismEndpoint 0 _) (relativeHomArrowPrism q r)
    (leftFibrationCoherentEvaluation a.val), relativeHomArrowPrism_zero q r,
    SSet.const_comp, SSet.comp_const]

/-- pointed 四角形の始点側の短辺の終点を、実際の終点 fiber へ入れる。 -/
def relativeHomPointedSourceEndpoint {B : SSet.{u}} (a q r : LeftFibrationObject B)
    (W : _ ⟶ PointedSpaceInfinity.{u})
    (hW : W ≫ pointedSpaceProjection = relativeHomCoherentNaturalitySquare a q r) :
    (SSet.uliftFunctor.{u + 1, u}).obj (relativeFunctorSpace r.val.hom q.val.hom) ⊗
      pinchedHom (functorVertex (leftFibrationCoherentEvaluation q.val))
        (functorVertex (leftFibrationCoherentEvaluation a.val)) ⟶
    vertexFiber pointedSpaceProjection
      ((leftFibrationCoherentEvaluation a.val).app (Opposite.op ⦋0⦌) (coherentNerveVertex q)) :=
  vertexFiberLift _ _ (prismEndpoint 1 _ ≫ (Δ[1] ◁ prismEndpoint 0 _) ≫ W) (by
    rw [Category.assoc, Category.assoc, hW]
    exact relativeHomPointedSourcePrism_one a q r)

/-- 同じ pointed 短辺の終点は、実際の coherent 評価の普遍輸送を恒等射で評価した族と同型。 -/
def relativeHomPointedSourceEndpoint_transportIso {B : SSet.{u}}
    (a q r : LeftFibrationObject B) (W : _ ⟶ PointedSpaceInfinity.{u})
    (hW : W ≫ pointedSpaceProjection = relativeHomCoherentNaturalitySquare a q r)
    (h₀ : prismEndpoint 0 _ ≫ prismEndpoint 0 _ ≫ W = relativeHomPointedIdentityFamily q _) :
    FunctorIso (relativeHomPointedSourceEndpoint a q r W hW)
      (diagonalFiberTransport pointedSpaceProjection
        (SSet.const (relativeHomPointedIdentity q))
        (intervalMappingCurryOfEndpoints (relativeHomPointedSourcePrism a q r)
          (relativeHomPointedSourcePrism_zero a q r)
          (relativeHomPointedSourcePrism_one a q r))) := by
  apply leftFibrationPrism_diagonalTransportIso pointedSpaceProjection
    (SSet.const (relativeHomPointedIdentity q)) (relativeHomPointedSourceEndpoint a q r W hW)
    (relativeHomPointedSourcePrism a q r) (relativeHomPointedSourcePrism_zero a q r)
    (relativeHomPointedSourcePrism_one a q r) ((Δ[1] ◁ prismEndpoint 0 _) ≫ W)
  · rw [← Category.assoc, prismEndpoint_square_exchange, Category.assoc]
    exact h₀
  · exact (vertexFiberLift_ι _ _ _ _).symm
  · rw [Category.assoc, hW]
    rfl

/-- 元の Hom 関手の作用を被覆する、自然性の最初の横辺。 -/
def relativeHomPointedInitialRowPrism {B : SSet.{u}} (a q r : LeftFibrationObject B) :=
  prismEndpoint 0 _ ≫ relativeHomCoherentNaturalitySquare a q r

/-- 最初の横辺も、同じ自己 Hom の空間から始まる。 -/
lemma relativeHomPointedInitialRowPrism_zero {B : SSet.{u}} (a q r : LeftFibrationObject B) :
    prismEndpoint 0 _ ≫ relativeHomPointedInitialRowPrism a q r =
      SSet.const (spaceInfinityVertex (relativeHomIdentityKanObject q)) :=
  relativeHomCoherentNaturalitySquare_origin a q r

/-- 最初の横辺の終点は、各標的で評価した元の Hom 関手。 -/
lemma relativeHomPointedInitialRowPrism_one {B : SSet.{u}} (a q r : LeftFibrationObject B) :
    prismEndpoint 1 _ ≫ relativeHomPointedInitialRowPrism a q r =
      SSet.const ((leftFibrationCoherentEvaluation q.val).app (Opposite.op ⦋0⦌)
        (coherentNerveVertex r)) := by
  rw [relativeHomPointedInitialRowPrism,
    relativeHomCoherentNaturalitySquare_transformation_zero,
    ← Category.assoc, prismEndpoint_naturality, Category.assoc]
  rw [← Category.assoc (prismEndpoint 1 _) (relativeHomArrowPrism q r)
    (leftFibrationCoherentEvaluation q.val), relativeHomArrowPrism_one q r,
    SSet.const_comp, SSet.comp_const]

/-- pointed 四角形の最初の横辺の終点を、実際の標的 fiber へ入れる。 -/
def relativeHomPointedInitialRowEndpoint {B : SSet.{u}} (a q r : LeftFibrationObject B)
    (W : _ ⟶ PointedSpaceInfinity.{u})
    (hW : W ≫ pointedSpaceProjection = relativeHomCoherentNaturalitySquare a q r) :
    (SSet.uliftFunctor.{u + 1, u}).obj (relativeFunctorSpace r.val.hom q.val.hom) ⊗
      pinchedHom (functorVertex (leftFibrationCoherentEvaluation q.val))
        (functorVertex (leftFibrationCoherentEvaluation a.val)) ⟶
    vertexFiber pointedSpaceProjection
      ((leftFibrationCoherentEvaluation q.val).app (Opposite.op ⦋0⦌) (coherentNerveVertex r)) :=
  vertexFiberLift _ _ (prismEndpoint 1 _ ≫ prismEndpoint 0 _ ≫ W) (by
    rw [Category.assoc, Category.assoc, hW]
    exact relativeHomPointedInitialRowPrism_one a q r)

/-- 同じ最初の横辺の終点は、元の Hom の作用の普遍輸送を恒等射で評価した族と同型。 -/
def relativeHomPointedInitialRowEndpoint_transportIso {B : SSet.{u}}
    (a q r : LeftFibrationObject B) (W : _ ⟶ PointedSpaceInfinity.{u})
    (hW : W ≫ pointedSpaceProjection = relativeHomCoherentNaturalitySquare a q r)
    (h₀ : prismEndpoint 0 _ ≫ prismEndpoint 0 _ ≫ W = relativeHomPointedIdentityFamily q _) :
    FunctorIso (relativeHomPointedInitialRowEndpoint a q r W hW)
      (diagonalFiberTransport pointedSpaceProjection
        (SSet.const (relativeHomPointedIdentity q))
        (intervalMappingCurryOfEndpoints (relativeHomPointedInitialRowPrism a q r)
          (relativeHomPointedInitialRowPrism_zero a q r)
          (relativeHomPointedInitialRowPrism_one a q r))) := by
  apply leftFibrationPrism_diagonalTransportIso pointedSpaceProjection
    (SSet.const (relativeHomPointedIdentity q)) (relativeHomPointedInitialRowEndpoint a q r W hW)
    (relativeHomPointedInitialRowPrism a q r) (relativeHomPointedInitialRowPrism_zero a q r)
    (relativeHomPointedInitialRowPrism_one a q r) (prismEndpoint 0 _ ≫ W)
  · exact h₀
  · exact (vertexFiberLift_ι _ _ _ _).symm
  · rw [Category.assoc, hW]
    rfl

end SerrePositivity.InfinityCategories
