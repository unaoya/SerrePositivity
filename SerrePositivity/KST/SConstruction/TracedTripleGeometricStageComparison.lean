module
public import SerrePositivity.KST.SConstruction.TracedTripleGeometricStagePasting

/-! # 元の指定第四辺と生成第四辺の実幾何消去からの段比較
概要：六対角面の実消去の出力を、元の両 BF 辺の同じ全 raw 段評価へ戻す。
方針：両全一単体の厳密な回収式だけで円柱の端点表示を合わせる。
規約：実四面体・元の全正規化・元の全十二面を保持し、隣接段適合は主張しない。
使われ方：全高次 prism に沿う相対選択へ渡す元の各段の実比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet Spectra
open scoped Simplicial
variable {I : Type u} [SmallCategory I] (F : I ⥤ StableModel.{u})
  {w x y z : I} (f : w ⟶ x) (g : x ⟶ y) (h : y ⟶ z)

/-- 実消去の始辺全体は元の指定 BF 辺の同じ全 raw 段評価。 -/
lemma monicKTracedTripleGeometricStageCylinder_source (n : ℕ) :
    SSet.yonedaEquiv.symm (monicKTracedTripleLeftStageEdgeData F f g h n).second.edge =
      SSet.yonedaEquiv.symm (((monicKTracedNativeTriplePrescribedEdge F f g h).map
        (kRawMappingProjection (F.obj w) (F.obj z) ≫
          RawSpectrumMapping.evaluation (kOmegaSpectrum (F.obj w))
            (kKanSequence (F.obj z)) n))).edge := by
  rw [(monicKTracedTripleLeftStageEdgeData F f g h n).second_map,
    SSet.Edge.CompStruct.δ_zero_yonedaEquiv_symm,
    monicKTracedCompositionRawStageEdge_map, SSet.Edge.map_edge,
    ← SSet.yonedaEquiv_symm_comp, monicKTracedNativeTriplePrescribedEdge_edge]

/-- 実消去の終辺全体も元の生成 BF 辺の同じ全 raw 段評価。 -/
lemma monicKTracedTripleGeometricStageCylinder_target (n : ℕ) :
    SSet.yonedaEquiv.symm (monicKTracedTripleBFSecondEdgeData F f g h n).first.edge =
      SSet.yonedaEquiv.symm (((monicKTracedCoherentTripleGeneratedEdge F f g h).map
        (kRawMappingProjection (F.obj w) (F.obj z) ≫
          RawSpectrumMapping.evaluation (kOmegaSpectrum (F.obj w))
            (kKanSequence (F.obj z)) n))).edge := by
  rw [(monicKTracedTripleBFSecondEdgeData F f g h n).first_map,
    monicKTracedTripleRawSecondTriangle]
  simp only [← Category.assoc, SSet.Edge.CompStruct.δ_two_yonedaEquiv_symm]
  rw [SSet.Edge.map_edge, ← SSet.yonedaEquiv_symm_comp]
  exact Category.assoc _ _ _

/-- 元の同じ両 BF 辺の全 raw 段評価を結ぶ、実六対角面消去の全端点固定円柱。 -/
def monicKTracedTripleGeometricRawStageComparison (n : ℕ) :
    EndpointFixedEdgeCylinder ((monicKTracedNativeTriplePrescribedEdge F f g h).map
      (kRawMappingProjection (F.obj w) (F.obj z) ≫
        RawSpectrumMapping.evaluation (kOmegaSpectrum (F.obj w)) (kKanSequence (F.obj z)) n))
      ((monicKTracedCoherentTripleGeneratedEdge F f g h).map
      (kRawMappingProjection (F.obj w) (F.obj z) ≫
        RawSpectrumMapping.evaluation (kOmegaSpectrum (F.obj w)) (kKanSequence (F.obj z)) n)) where
  homotopy := familyHomotopyEndpointTransport
    (monicKTracedTripleGeometricStageCylinder F f g h n).homotopy
    (monicKTracedTripleGeometricStageCylinder_source F f g h n).symm
    (monicKTracedTripleGeometricStageCylinder_target F f g h n)
  relative := by
    rw [familyHomotopyEndpointTransport_h,
      (monicKTracedTripleGeometricStageCylinder F f g h n).relative,
      monicKTracedTripleGeometricStageCylinder_source]

/-- 両端の表示を戻しても、同じ実六対角面消去の全円柱を厳密に保持する。 -/
lemma monicKTracedTripleGeometricRawStageComparison_h (n : ℕ) :
    (monicKTracedTripleGeometricRawStageComparison F f g h n).homotopy.h =
      (monicKTracedTripleGeometricStageCylinder F f g h n).homotopy.h :=
  familyHomotopyEndpointTransport_h _ _ _

end SerrePositivity.KST.SConstruction
