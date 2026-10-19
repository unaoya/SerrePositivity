module
public import SerrePositivity.KST.SConstruction.KanAssemblyCompositionTriangle
public import SerrePositivity.KST.SConstruction.OneDirectionInverseCompositionTriangle

/-! # 因子の合成辺の一単体の回収
概要：端点を付け直した合成辺は、元の指定辺の移送と同じ一単体を持つ。
方針：辺の付け直しが一単体を変えないことを明示する。
規約：端点の等号の証明を展開して型推論に依存しない。
使われ方：合成三角形と交差正方形の共有辺の厳密な照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open scoped Simplicial

/-- 合成辺の端点の付け直しは移送した辺の一単体を保持する。 -/
lemma kanAssemblyCompositionFirstEdge_edge (r : ℕ) {X Y Z : StableModel.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (v : (kanAssemblyAdjointChoices r X) _⦋0⦌)
    (w : (kanAssemblyAdjointChoices r Y) _⦋0⦌)
    (e : (kanAssemblyMixedChoices r f).Edge
      ((kanAssemblyMixedFromSource r f).app (Opposite.op ⦋0⦌) v)
      ((kanAssemblyMixedFromTarget r f).app (Opposite.op ⦋0⦌) w)) :
    SSet.Edge.edge (X := kanAssemblyMixedChoices r (f ≫ g))
      (kanAssemblyCompositionFirstEdge r f g v w e) =
    (kanAssemblyMixedPost r f g).app (Opposite.op ⦋1⦌)
      (SSet.Edge.edge (X := kanAssemblyMixedChoices r f) e) := by
  dsimp only [kanAssemblyCompositionFirstEdge, SSet.Edge.ofEq, SSet.Edge.edge,
    SSet.Edge.toTruncated]
  rfl

/-- 合成辺の端点の付け直しは移送した辺の一単体を保持する。 -/
lemma kanAssemblyCompositionSecondEdge_edge (r : ℕ) {X Y Z : StableModel.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (w : (kanAssemblyAdjointChoices r Y) _⦋0⦌)
    (v : (kanAssemblyAdjointChoices r Z) _⦋0⦌)
    (e : (kanAssemblyMixedChoices r g).Edge
      ((kanAssemblyMixedFromSource r g).app (Opposite.op ⦋0⦌) w)
      ((kanAssemblyMixedFromTarget r g).app (Opposite.op ⦋0⦌) v)) :
    SSet.Edge.edge (X := kanAssemblyMixedChoices r (f ≫ g))
      (kanAssemblyCompositionSecondEdge r f g w v e) =
    (kanAssemblyMixedPre r f g).app (Opposite.op ⦋1⦌)
      (SSet.Edge.edge (X := kanAssemblyMixedChoices r g) e) := by
  dsimp only [kanAssemblyCompositionSecondEdge, SSet.Edge.ofEq, SSet.Edge.edge,
    SSet.Edge.toTruncated]
  rfl

/-- 合成辺の端点の付け直しは移送した辺の一単体を保持する。 -/
lemma oneDirectionInverseCompositionFirstEdge_edge (r : ℕ) {X Y Z : StableModel.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (v : (oneDirectionKanInverseChoices r X) _⦋0⦌)
    (w : (oneDirectionKanInverseChoices r Y) _⦋0⦌)
    (e : (oneDirectionInverseMixedChoices r f).Edge
      ((oneDirectionInverseMixedFromSource r f).app (Opposite.op ⦋0⦌) v)
      ((oneDirectionInverseMixedFromTarget r f).app (Opposite.op ⦋0⦌) w)) :
    SSet.Edge.edge (X := oneDirectionInverseMixedChoices r (f ≫ g))
      (oneDirectionInverseCompositionFirstEdge r f g v w e) =
    (oneDirectionInverseMixedPost r f g).app (Opposite.op ⦋1⦌)
      (SSet.Edge.edge (X := oneDirectionInverseMixedChoices r f) e) := by
  dsimp only [oneDirectionInverseCompositionFirstEdge, SSet.Edge.ofEq, SSet.Edge.edge,
    SSet.Edge.toTruncated]
  rfl

/-- 合成辺の端点の付け直しは移送した辺の一単体を保持する。 -/
lemma oneDirectionInverseCompositionSecondEdge_edge (r : ℕ) {X Y Z : StableModel.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (w : (oneDirectionKanInverseChoices r Y) _⦋0⦌)
    (v : (oneDirectionKanInverseChoices r Z) _⦋0⦌)
    (e : (oneDirectionInverseMixedChoices r g).Edge
      ((oneDirectionInverseMixedFromSource r g).app (Opposite.op ⦋0⦌) w)
      ((oneDirectionInverseMixedFromTarget r g).app (Opposite.op ⦋0⦌) v)) :
    SSet.Edge.edge (X := oneDirectionInverseMixedChoices r (f ≫ g))
      (oneDirectionInverseCompositionSecondEdge r f g w v e) =
    (oneDirectionInverseMixedPre r f g).app (Opposite.op ⦋1⦌)
      (SSet.Edge.edge (X := oneDirectionInverseMixedChoices r g) e) := by
  dsimp only [oneDirectionInverseCompositionSecondEdge, SSet.Edge.ofEq, SSet.Edge.edge,
    SSet.Edge.toTruncated]
  rfl

end SerrePositivity.KST.SConstruction
