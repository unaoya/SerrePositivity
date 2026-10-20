module
public import SerrePositivity.KST.SConstruction.TracedTripleTypedNormalizations
public import SerrePositivity.KST.SConstruction.TriangleEdgeTransport

/-! # 両正規化円柱に沿う元の外側二部分面の移送
概要：外側の元の全二部分三角形を、前後二射の指定済み補正辺へ移す。
方針：両端の表示を合わせ、元の正規化円柱を三辺移送の指定側面にする。
規約：元の全三角形と全正規化円柱を保持し、共有対角辺を全時刻固定する。
使われ方：元の十二面の六 diamond を同じ端点型で実消去へ渡す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet Spectra
open scoped Simplicial
variable {I : Type u} [SmallCategory I] (F : I ⥤ StableModel.{u})
  {w x y z : I} (f : w ⟶ x) (g : x ⟶ y) (h : y ⟶ z)

/-- 左外側の元の全面を、正規化終辺と元の交換辺で表示する。 -/
def monicKTracedTripleLeftBinaryEdgeData (n : ℕ) :=
  trianglePairEdgeData (monicKTracedTripleFirstTypedNormalization F f g h n).target
    (monicKTracedTripleInterchangeFirstLower F f g h n)
    (SSet.yonedaEquiv.symm (monicKPrismCompositeBinaryPointTriangle F (f ≫ g) h n).simplex)
    (monicKTracedTripleFirstTypedNormalization F f g h n).target_map.symm
    (monicKPrismCompositeBinaryPointTriangle_second_interchange F f g h n)

/-- 右外側の元の全面を、元の第一補正辺と正規化終辺で表示する。 -/
def monicKTracedTripleRightBinaryEdgeData (n : ℕ) :=
  trianglePairEdgeData (monicKTracedTripleFirstBinaryEdgeData F f g h n).first
    (monicKTracedTripleLastTypedNormalization F f g h n).target
    (SSet.yonedaEquiv.symm (monicKPrismCompositeBinaryPointTriangle F f (g ≫ h) n).simplex)
    ((monicKTracedTripleCorrectionPath_first F f g h n).symm.trans
      (monicKTracedTripleFirstBinaryEdgeData F f g h n).first_map.symm)
    (monicKTracedTripleLastTypedNormalization F f g h n).target_map.symm

/-- 元の左外側全面を同じ全正規化に沿って始端補正辺へ移す。 -/
def monicKTracedTripleLeftBinaryTransport (n : ℕ) :=
  triangleEdgeTransport (monicKTracedTripleFirstTypedNormalization F f g h n).cylinder
    (endpointFixedEdgeCylinderRefl (monicKTracedTripleInterchangeFirstLower F f g h n))
    (endpointFixedEdgeCylinderRefl (monicKTracedTripleLeftBinaryEdgeData F f g h n).direct)
    (monicKTracedTripleLeftBinaryEdgeData F f g h n).triangle

/-- 元の右外側全面も同じ全正規化に沿って始端補正辺へ移す。 -/
def monicKTracedTripleRightBinaryTransport (n : ℕ) :=
  triangleEdgeTransport
    (endpointFixedEdgeCylinderRefl (monicKTracedTripleFirstBinaryEdgeData F f g h n).first)
    (monicKTracedTripleLastTypedNormalization F f g h n).cylinder
    (endpointFixedEdgeCylinderRefl (monicKTracedTripleRightBinaryEdgeData F f g h n).direct)
    (monicKTracedTripleRightBinaryEdgeData F f g h n).triangle

/-- 左移送の元の全三角形へ戻る実比較円柱。 -/
def monicKTracedTripleLeftBinaryTransportComparison (n : ℕ) :=
  triangleEdgeTransportComparison (monicKTracedTripleFirstTypedNormalization F f g h n).cylinder
    (endpointFixedEdgeCylinderRefl (monicKTracedTripleInterchangeFirstLower F f g h n))
    (endpointFixedEdgeCylinderRefl (monicKTracedTripleLeftBinaryEdgeData F f g h n).direct)
    (monicKTracedTripleLeftBinaryEdgeData F f g h n).triangle

/-- 右移送の元の全三角形へ戻る実比較円柱。 -/
def monicKTracedTripleRightBinaryTransportComparison (n : ℕ) :=
  triangleEdgeTransportComparison
    (endpointFixedEdgeCylinderRefl (monicKTracedTripleFirstBinaryEdgeData F f g h n).first)
    (monicKTracedTripleLastTypedNormalization F f g h n).cylinder
    (endpointFixedEdgeCylinderRefl (monicKTracedTripleRightBinaryEdgeData F f g h n).direct)
    (monicKTracedTripleRightBinaryEdgeData F f g h n).triangle

end SerrePositivity.KST.SConstruction
