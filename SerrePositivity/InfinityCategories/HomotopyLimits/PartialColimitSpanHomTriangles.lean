module

public import SerrePositivity.InfinityCategories.HomotopyLimits.PartialColimitSpanPointTransport
public import SerrePositivity.InfinityCategories.HomotopyLimits.CoconeTransportTriangleHom

/-!
概要：普遍 span の左右の輸送余錐の全 Hom 族を、同じ共通余錐の Hom 比較へ接続する。
方針：元の左右二単体をそのまま使い、両終点の底を同じ native な span 頂点へ揃える。
規約：パラメータは両側で同じ全 Hom。元の評価固定円柱を保持し、終点の余極限性は仮定しない。
使われ方：指定比較経路と実際の両枝の Hom 係数との高次整合性。
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
local notation "z" => JoinCocone.vertex
  (partialColimitStrictSpanCocone c hc i F hi dB j G hj dC)
local notation "σL" => partialColimitSpanLeftTriangle c hc i F hi dB j G hj dC
local notation "σR" => partialColimitSpanRightTriangle c hc i F hi dB j G hj dC
local notation "q" => sliceUnderProjection p

/-- 共通余錐を左の実際の二辺で輸送した、元の図式上の余錐。 -/
def partialColimitSpanLeftTransportCocone : JoinCocone p :=
  coconeTransportTriangleTerminal c
    (e := SSet.Edge.ofTruncated (colimitAttachmentApexEdge c hc i F hi dB))
    (f := partialColimitSpanLeftLeg c hc i F hi dB j G hj dC)

/-- 同じ共通余錐を右の実際の二辺で輸送した余錐。 -/
def partialColimitSpanRightTransportCocone : JoinCocone p :=
  coconeTransportTriangleTerminal c
    (e := SSet.Edge.ofTruncated (colimitAttachmentApexEdge c hc j G hj dC))
    (f := partialColimitSpanRightLeg c hc i F hi dB j G hj dC)

/-- 左輸送余錐の頂点は、元の native な普遍 span の頂点そのもの。 -/
lemma partialColimitSpanLeftTransportCocone_vertex :
    (partialColimitSpanLeftTransportCocone c hc i F hi dB j G hj dC).vertex = z :=
  coconeTransportTriangleTerminal_vertex _

/-- 右輸送余錐の頂点も、同じ普遍 span の頂点そのもの。 -/
lemma partialColimitSpanRightTransportCocone_vertex :
    (partialColimitSpanRightTransportCocone c hc i F hi dB j G hj dC).vertex = z :=
  coconeTransportTriangleTerminal_vertex _

variable (y : SpaceInfinity.{u} _⦋0⦌)

/-- 同じ span 頂点からの全 Hom 上に表示した左輸送余錐の族。 -/
def partialColimitSpanLeftTransportHomFamily : pinchedHomLeft z y ⟶ coconeMappingSpace p y :=
  coconeTransportTrianglePointHomFamily c
    (e := SSet.Edge.ofTruncated (colimitAttachmentApexEdge c hc i F hi dB))
    (f := partialColimitSpanLeftLeg c hc i F hi dB j G hj dC) y

/-- 全く同じ全 Hom 上に表示した右輸送余錐の族。 -/
def partialColimitSpanRightTransportHomFamily : pinchedHomLeft z y ⟶ coconeMappingSpace p y :=
  coconeTransportTrianglePointHomFamily c
    (e := SSet.Edge.ofTruncated (colimitAttachmentApexEdge c hc j G hj dC))
    (f := partialColimitSpanRightLeg c hc i F hi dB j G hj dC) y

/-- 左族の共通余錐による Hom 比較を、元の左二単体全体の族と結ぶ実際の円柱。 -/
def partialColimitSpanLeftTransportHomComparison : SSet.Homotopy
    (partialColimitSpanLeftTransportHomFamily c hc i F hi dB j G hj dC y ≫
      coconeMappingSpaceHomComparison c hc y)
    (coconeTransportTriangleInitialHomFamily c σL y ≫ leftFibrationInitialProjection q c y ≫
      (leftFibrationInitialBaseIso q c y).hom) :=
  coconeTransportTriangleHomComparison c hc σL y

/-- 右族の Hom 比較も、同じ共通余錐と元の右二単体で表示する実際の円柱。 -/
def partialColimitSpanRightTransportHomComparison : SSet.Homotopy
    (partialColimitSpanRightTransportHomFamily c hc i F hi dB j G hj dC y ≫
      coconeMappingSpaceHomComparison c hc y)
    (coconeTransportTriangleInitialHomFamily c σR y ≫ leftFibrationInitialProjection q c y ≫
      (leftFibrationInitialBaseIso q c y).hom) :=
  coconeTransportTriangleHomComparison c hc σR y

/-- 左 Hom 比較の円柱は、同じ評価固定の中間円柱の像を保持する。 -/
lemma partialColimitSpanLeftTransportHomComparison_projection :
    (partialColimitSpanLeftTransportHomComparison c hc i F hi dB j G hj dC y).h =
      (coconeTransportTriangleInitialComparison c hc σL y).h ≫
        leftFibrationInitialProjection q c y ≫ (leftFibrationInitialBaseIso q c y).hom :=
  coconeTransportTriangleHomComparison_projection _ _ _ _

/-- 右 Hom 比較も、元の評価固定の中間円柱を保持する。 -/
lemma partialColimitSpanRightTransportHomComparison_projection :
    (partialColimitSpanRightTransportHomComparison c hc i F hi dB j G hj dC y).h =
      (coconeTransportTriangleInitialComparison c hc σR y).h ≫
        leftFibrationInitialProjection q c y ≫ (leftFibrationInitialBaseIso q c y).hom :=
  coconeTransportTriangleHomComparison_projection _ _ _ _

/-- 二つの実際の輸送余錐を結ぶ経路は、同じ指定済みの輸送経路そのもの。 -/
def partialColimitSpanTransportCoconePath :
    (Δ[0] : SSet.{u + 1}) ⟶ equivalencePath (coconeMappingSpace p z) :=
  partialColimitSpanTransportPointPath c hc i F hi dB j G hj dC q
    (coconeTransportTriangleInitialVertex c)

/-- 指定経路の始点は、左の実際の輸送余錐を同じ頂点上に表示したもの。 -/
lemma partialColimitSpanTransportCoconePath_zero :
    partialColimitSpanTransportCoconePath c hc i F hi dB j G hj dC ≫
      equivalencePathEndpoint _ 0 = SSet.yonedaEquiv.symm
        (initialFiberVertexAt q (partialColimitSpanLeftTransportCocone
          c hc i F hi dB j G hj dC) z
          (partialColimitSpanLeftTransportCocone_vertex c hc i F hi dB j G hj dC)) := by
  refine (partialColimitSpanTransportPointPath_zero
    c hc i F hi dB j G hj dC q (coconeTransportTriangleInitialVertex c)).trans ?_
  apply congrArg SSet.yonedaEquiv.symm
  apply Subtype.ext
  rfl

/-- 同じ経路の終点は、右の実際の輸送余錐を同じ頂点上に表示したもの。 -/
lemma partialColimitSpanTransportCoconePath_one :
    partialColimitSpanTransportCoconePath c hc i F hi dB j G hj dC ≫
      equivalencePathEndpoint _ 1 = SSet.yonedaEquiv.symm
        (initialFiberVertexAt q (partialColimitSpanRightTransportCocone
          c hc i F hi dB j G hj dC) z
          (partialColimitSpanRightTransportCocone_vertex c hc i F hi dB j G hj dC)) := by
  refine (partialColimitSpanTransportPointPath_one
    c hc i F hi dB j G hj dC q (coconeTransportTriangleInitialVertex c)).trans ?_
  apply congrArg SSet.yonedaEquiv.symm
  apply Subtype.ext
  rfl

end
end SerrePositivity.InfinityCategories.HomotopyLimits
