module
public import SerrePositivity.KST.SConstruction.TracedBFTripleEdgeTransport
public import SerrePositivity.KST.SConstruction.EndpointFixedCylinderLifting

/-! # 生成第四辺と元の指定 BF 比較辺の同じ raw 境界問題
概要：元の指定左比較辺を同じ始点表示へ移し、生成第四辺との全端点固定 raw 比較を定める。
方針：圏の結合則は頂点表示だけに使い、両全辺を同じ実 raw 射影で写す。
規約：raw 比較の存在は未証明。型の定義や持ち上げ可能性を完成した coherence と数えない。
使われ方：元の高次 prism から構成すべき実円柱の厳密な両端と固定境界。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet Spectra
open scoped Simplicial
local instance tracedTripleRawBoundarySpectrumSimplicialCategory :
    SimplicialCategory OmegaSpectrum.{u} := OmegaSpectrum.simplicialCategory
variable {I : Type u} [SmallCategory I] (F : I ⥤ StableModel.{u})
  {w x y z : I} (f : w ⟶ x) (g : x ⟶ y) (h : y ⟶ z)

/-- 独立に指定した元の左 BF 比較辺。全辺を変えずに合成入力の括弧だけを合わせる。 -/
def monicKTracedNativeTriplePrescribedEdgeData :=
  edgeSourceTransportData (monicKTracedSpectrumCompositionEdge F (f ≫ g) h)
    (congrArg (fun k => SimplicialCategory.homEquiv' _ _ (monicKTracedSpectrumMap F k))
      (Category.assoc f g h))

/-- 元の指定左 BF 辺の表示移送。元の全辺の等号は同じデータに保存する。 -/
def monicKTracedNativeTriplePrescribedEdge :=
  (monicKTracedNativeTriplePrescribedEdgeData F f g h).val

/-- 合成入力の括弧を合わせても、元の指定 BF 比較辺の全一単体を変更しない。 -/
lemma monicKTracedNativeTriplePrescribedEdge_edge :
    (monicKTracedNativeTriplePrescribedEdge F f g h).edge =
      (monicKTracedSpectrumCompositionEdge F (f ≫ g) h).edge :=
  (monicKTracedNativeTriplePrescribedEdgeData F f g h).property

/-- 元の指定比較辺から生成第四辺への、同じ raw 射影上の全端点固定比較問題。 -/
abbrev MonicKTracedTripleRawComparison :=
  EndpointFixedEdgeCylinder
    ((monicKTracedNativeTriplePrescribedEdge F f g h).map
      (kRawMappingProjection (F.obj w) (F.obj z)))
    ((monicKTracedCoherentTripleGeneratedEdge F f g h).map
      (kRawMappingProjection (F.obj w) (F.obj z)))

/-- 元の全 BF 比較を全境界固定で構成できることと、同じ raw 比較の存在は同値。 -/
lemma monicKTracedTripleRawComparison_nonempty_iff :
    Nonempty (EndpointFixedEdgeCylinder (monicKTracedNativeTriplePrescribedEdge F f g h)
      (monicKTracedCoherentTripleGeneratedEdge F f g h)) ↔
        Nonempty (MonicKTracedTripleRawComparison F f g h) :=
  endpointFixedCylinder_nonempty_iff _ _ _ (kRawMappingProjection_rlp _ _)

/-- 元の raw 比較が与えられれば、その全円柱と元の両辺を保つ BF 比較を得る。 -/
def monicKTracedTripleFourthEdgeLiftData (H : MonicKTracedTripleRawComparison F f g h) :=
  endpointFixedCylinderLiftData (monicKTracedNativeTriplePrescribedEdge F f g h)
    (monicKTracedCoherentTripleGeneratedEdge F f g h)
    (kRawMappingProjection (F.obj w) (F.obj z)) (kRawMappingProjection_rlp _ _) H

/-- 持ち上げた BF 円柱の全 raw 射影は、与えられた同じ元の全 raw 円柱。 -/
lemma monicKTracedTripleFourthEdgeLiftData_projection
    (H : MonicKTracedTripleRawComparison F f g h) :
    (monicKTracedTripleFourthEdgeLiftData F f g h H).val.homotopy.h ≫
        kRawMappingProjection (F.obj w) (F.obj z) = H.homotopy.h :=
  (monicKTracedTripleFourthEdgeLiftData F f g h H).property

end SerrePositivity.KST.SConstruction
