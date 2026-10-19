module

public import SerrePositivity.InfinityCategories.HomotopyLimits.PartialColimitSpanTriangles
public import SerrePositivity.InfinityCategories.HomotopyLimits.CoherentTransportTriangleVertex

/-!
概要：普遍 span の左右の実際の輸送終点を、同じ fiber の二頂点として保持する。
方針：元の二つの三角形 prism を同じ始点で評価し、指定済みの同じ境界経路を制限する。
規約：両終点は同じ native な span 頂点上。経路を新たに選ばない。
使われ方：左右の全 Hom の三角形族を同じ Hom パラメータ上で照合する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {A B C : SSet.{u + 1}} {p : A ⟶ SpaceInfinity.{u}}
  (c : JoinCocone p) (hc : IsColimitCone c)
  (i : A ⟶ B) (F : B ⟶ SpaceInfinity.{u}) (hi : i ≫ F = p) (dB : JoinCocone F)
  (j : A ⟶ C) (G : C ⟶ SpaceInfinity.{u}) (hj : j ≫ G = p) (dC : JoinCocone G)
  {E : SSet.{u + 1}} (q : E ⟶ SpaceInfinity.{u}) [LeftFibration q]
  (v : (vertexFiber q c.vertex) _⦋0⦌)
local notation "z" => JoinCocone.vertex
  (partialColimitStrictSpanCocone c hc i F hi dB j G hj dC)

/-- 左の実際の二段階輸送の終点を、元の span 頂点上の fiber の頂点として保持する。 -/
def partialColimitSpanLeftTransportVertex : (vertexFiber q z) _⦋0⦌ :=
  (edgeTransport q (colimitAttachmentApexEdge c hc i F hi dB) ≫
    edgeTransport q (partialColimitSpanLeftLeg c hc i F hi dB j G hj dC)).app _ v

/-- 右の実際の二段階輸送の終点も、全く同じ span 頂点上の fiber に属する。 -/
def partialColimitSpanRightTransportVertex : (vertexFiber q z) _⦋0⦌ :=
  (edgeTransport q (colimitAttachmentApexEdge c hc j G hj dC) ≫
    edgeTransport q (partialColimitSpanRightLeg c hc i F hi dB j G hj dC)).app _ v

/-- 左の点の三角形は、元の span の左二単体を同じ始点で持ち上げたもの。 -/
def partialColimitSpanLeftTransportTriangle : (Δ[2] : SSet.{u + 1}) ⟶ E :=
  coherentTransportTriangleVertex q (partialColimitSpanLeftTriangle c hc i F hi dB j G hj dC) v

/-- 右の点の三角形も、元の span の右二単体を同じ始点で持ち上げたもの。 -/
def partialColimitSpanRightTransportTriangle : (Δ[2] : SSet.{u + 1}) ⟶ E :=
  coherentTransportTriangleVertex q (partialColimitSpanRightTriangle c hc i F hi dB j G hj dC) v

/-- 左三角形は、元の左二単体を厳密に被覆する。 -/
lemma partialColimitSpanLeftTransportTriangle_projection :
    partialColimitSpanLeftTransportTriangle c hc i F hi dB j G hj dC q v ≫ q =
      SSet.yonedaEquiv.symm (partialColimitSpanLeftTriangle c hc i F hi dB j G hj dC).simplex :=
  coherentTransportTriangleVertex_projection _ _ _

/-- 右三角形は、元の右二単体を厳密に被覆する。 -/
lemma partialColimitSpanRightTransportTriangle_projection :
    partialColimitSpanRightTransportTriangle c hc i F hi dB j G hj dC q v ≫ q =
      SSet.yonedaEquiv.symm (partialColimitSpanRightTriangle c hc i F hi dB j G hj dC).simplex :=
  coherentTransportTriangleVertex_projection _ _ _

/-- 元の二単体の合成比較を、同じ始点の二つの実際の終点で評価した同型。 -/
def partialColimitSpanTransportPointIso :
    FunctorIso
      (SSet.yonedaEquiv.symm (partialColimitSpanLeftTransportVertex
        c hc i F hi dB j G hj dC q v))
      (SSet.yonedaEquiv.symm (partialColimitSpanRightTransportVertex
        c hc i F hi dB j G hj dC q v)) := by
  simpa only [partialColimitSpanLeftTransportVertex, partialColimitSpanRightTransportVertex,
    SSet.yonedaEquiv_symm_comp] using FunctorIso.precomp
      (partialColimitSpanTransportIso c hc i F hi dB j G hj dC q) (SSet.yonedaEquiv.symm v)

/-- 左右の終点を結ぶ経路は、指定済みの同じ全パラメータ経路の頂点での制限。 -/
def partialColimitSpanTransportPointPath :
    (Δ[0] : SSet.{u + 1}) ⟶ equivalencePath (vertexFiber q z) :=
  SSet.yonedaEquiv.symm v ≫ partialColimitSpanTransportPath c hc i F hi dB j G hj dC q

/-- 指定経路の始点は、同じ実際の左終点。 -/
lemma partialColimitSpanTransportPointPath_zero :
    partialColimitSpanTransportPointPath c hc i F hi dB j G hj dC q v ≫
      equivalencePathEndpoint _ 0 = SSet.yonedaEquiv.symm
        (partialColimitSpanLeftTransportVertex c hc i F hi dB j G hj dC q v) := by
  rw [partialColimitSpanTransportPointPath, Category.assoc, partialColimitSpanTransportPath_zero,
    SSet.yonedaEquiv_symm_comp]
  rfl

/-- 指定経路の終点は、同じ実際の右終点。 -/
lemma partialColimitSpanTransportPointPath_one :
    partialColimitSpanTransportPointPath c hc i F hi dB j G hj dC q v ≫
      equivalencePathEndpoint _ 1 = SSet.yonedaEquiv.symm
        (partialColimitSpanRightTransportVertex c hc i F hi dB j G hj dC q v) := by
  rw [partialColimitSpanTransportPointPath, Category.assoc, partialColimitSpanTransportPath_one,
    SSet.yonedaEquiv_symm_comp]
  rfl

end
end SerrePositivity.InfinityCategories.HomotopyLimits
