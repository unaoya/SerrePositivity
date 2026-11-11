module
public import SerrePositivity.KST.SConstruction.TracedCompositePartBoundaries

/-! # 元の合成補正の二部分の全合成木
概要：元の前後二本の単一射補正の全木を同じ合成空間へ写し、同じ中間族で接続する。
方針：保存済みの同じ全証人を後合成し、全端点の厳密な式で表示だけを移す。
規約：各全円柱・全入力区間・全三角形を元の同じ像として保持する。
使われ方：元の全合成補正を、元の二本の単一射円柱を二辺に持つ実三角形へまとめる。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet Spectra Spectra.PointedMapping
open SerrePositivity.InfinityCategories
open scoped Simplicial
variable {I : Type u} [SmallCategory I] (F : I ⥤ StableModel.{u})
  {x y z : I} (f : x ⟶ y) (g : y ⟶ z)

/-- 前の単一射の同じ全木を、元の後続段射で後合成した第一部分。 -/
def monicKPrismCompositePointFirstData (n : ℕ) :=
  ((monicKPrismUnaryConstantPointData F f n).map
    (PointedObject.basedHomMap ((kOmegaSpectrum (F.obj x)).level n).space
      (kKanSequenceLevelMap (F.map g) n)).right).endpointTransport
        (monicKPrismCompositePart_source F f g n) rfl

/-- 後の単一射の同じ全木を、前の BF 段頂点と合成した第二部分。 -/
def monicKPrismCompositePointSecondData (n : ℕ) :=
  ((monicKPrismUnaryConstantPointData F g n).map
    (monicKTracedTripleLastPairStageMap F f z n)).endpointTransport
      (monicKPrismCompositePart_middle F f g n) rfl

/-- 元の同じ全合成補正を、二部分と同じ定数始点・同じ終点表示で保持する。 -/
def monicKPrismCompositeConstantPointData (n : ℕ) :=
  (monicKPrismCompositePointData F f g n).endpointTransport
    (SSet.comp_const (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint (compositionStringDirect f g))
      (familyVertex (monicKToRawLevelMap (F.map (f ≫ g)) n))).symm
    (monicKPrismCompositePart_target F f g n)

/-- 第一部分の全円柱は、前の同じ単一射補正の後合成像そのもの。 -/
lemma monicKPrismCompositePointFirstData_h (n : ℕ) :
    (monicKPrismCompositePointFirstData F f g n).homotopy.h =
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint (coherentArrowStringDirect f) ▷ (Δ[1] : SSet.{u})) ≫
        (monicKPrismUnaryCorrectionData F f n).homotopy.h) ≫
          (PointedObject.basedHomMap ((kOmegaSpectrum (F.obj x)).level n).space
            (kKanSequenceLevelMap (F.map g) n)).right := by
  rw [monicKPrismCompositePointFirstData, FamilyChainCompositeData.endpointTransport_h,
    FamilyChainCompositeData.map_h, monicKPrismUnaryConstantPointData_h]

/-- 第二部分の全円柱も、後の同じ単一射補正と同じ BF 頂点の実合成像。 -/
lemma monicKPrismCompositePointSecondData_h (n : ℕ) :
    (monicKPrismCompositePointSecondData F f g n).homotopy.h =
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint (coherentArrowStringDirect g) ▷ (Δ[1] : SSet.{u})) ≫
        (monicKPrismUnaryCorrectionData F g n).homotopy.h) ≫
          monicKTracedTripleLastPairStageMap F f z n := by
  rw [monicKPrismCompositePointSecondData, FamilyChainCompositeData.endpointTransport_h,
    FamilyChainCompositeData.map_h, monicKPrismUnaryConstantPointData_h]

/-- 元の全列の円柱は、表示移送でも同じ全一点制限を保持する。 -/
lemma monicKPrismCompositeConstantPointData_h (n : ℕ) :
    (monicKPrismCompositeConstantPointData F f g n).homotopy.h =
      (monicKPrismCompositePointData F f g n).homotopy.h :=
  FamilyChainCompositeData.endpointTransport_h _ _ _

/-- 元の第二 trace は、同じ BF 段頂点の全 Hom 合成で後の全 trace を写したもの。 -/
lemma monicKPrismCompositePointSecondTrace_map (n : ℕ) :
    monicKPrismCompositePointSecondTrace F f g n =
      (monicKPrismUnaryPointTrace F g n).map
        (· ≫ monicKTracedTripleLastPairStageMap F f z n) := by
  unfold monicKPrismCompositePointSecondTrace
  apply List.map_congr_left
  intro h _
  have hf : fst (Δ[0] : SSet.{u}) Δ[1] ≫ monicKPrismTracedBFBoundary F f ≫
      OmegaSpectrum.evaluation (kOmegaSpectrum (F.obj x)) (kOmegaSpectrum (F.obj y)) n =
      SSet.const (monicKTracedBFStageVertex F f n) := by
    rw [monicKPrismTracedBFBoundary_stage_const, SSet.comp_const]
  rw [hf]
  exact (pointedFixedLeftVertexComposition_apply (monicKTracedBFStageVertex F f n) h).symm

/-- 第一部分の全木は、元の同じ第一 trace を厳密に回収する。 -/
lemma monicKPrismCompositePointFirstData_trace (n : ℕ) :
    familyChainCompositionInputTrace (monicKPrismCompositePointFirstData F f g n).witness =
      monicKPrismCompositePointFirstTrace F f g n := by
  rw [monicKPrismCompositePointFirstData, FamilyChainCompositeData.endpointTransport_trace,
    FamilyChainCompositeData.map_trace, monicKPrismUnaryConstantPointData_trace]
  rfl

/-- 第二部分の全木も、元の同じ第二 trace を厳密に回収する。 -/
lemma monicKPrismCompositePointSecondData_trace (n : ℕ) :
    familyChainCompositionInputTrace (monicKPrismCompositePointSecondData F f g n).witness =
      monicKPrismCompositePointSecondTrace F f g n := by
  rw [monicKPrismCompositePointSecondData, FamilyChainCompositeData.endpointTransport_trace,
    FamilyChainCompositeData.map_trace, monicKPrismUnaryConstantPointData_trace]
  exact (monicKPrismCompositePointSecondTrace_map F f g n).symm

/-- 元の全列の全木は、両部分の元の全区間を同じ順序で保持する。 -/
lemma monicKPrismCompositeConstantPointData_trace (n : ℕ) :
    familyChainCompositionInputTrace (monicKPrismCompositeConstantPointData F f g n).witness =
      monicKPrismCompositePointFirstTrace F f g n ++
        monicKPrismCompositePointSecondTrace F f g n := by
  rw [monicKPrismCompositeConstantPointData, FamilyChainCompositeData.endpointTransport_trace]
  exact monicKPrismCompositePointData_trace F f g n

/-- 第一部分は、前の元の全合成三角形の同じ一点制限・後合成像を全て保持する。 -/
lemma monicKPrismCompositePointFirstData_triangles (n : ℕ) :
    familyChainCompositionTriangles (monicKPrismCompositePointFirstData F f g n).witness =
      (familyChainCompositionTriangles (monicKPrismUnaryConstantPointData F f n).witness).map
        (· ≫ (PointedObject.basedHomMap ((kOmegaSpectrum (F.obj x)).level n).space
          (kKanSequenceLevelMap (F.map g) n)).right) := by
  rw [monicKPrismCompositePointFirstData, FamilyChainCompositeData.endpointTransport_triangles,
    FamilyChainCompositeData.map_triangles]

/-- 第二部分も、後の元の全合成三角形の同じ一点制限・実合成像を全て保持する。 -/
lemma monicKPrismCompositePointSecondData_triangles (n : ℕ) :
    familyChainCompositionTriangles (monicKPrismCompositePointSecondData F f g n).witness =
      (familyChainCompositionTriangles (monicKPrismUnaryConstantPointData F g n).witness).map
        (· ≫ monicKTracedTripleLastPairStageMap F f z n) := by
  rw [monicKPrismCompositePointSecondData, FamilyChainCompositeData.endpointTransport_triangles,
    FamilyChainCompositeData.map_triangles]

/-- 元の全列の合成木自体も、端点表示移送で変更しない。 -/
lemma monicKPrismCompositeConstantPointData_triangles (n : ℕ) :
    familyChainCompositionTriangles (monicKPrismCompositeConstantPointData F f g n).witness =
      familyChainCompositionTriangles (monicKPrismCompositePointData F f g n).witness :=
  FamilyChainCompositeData.endpointTransport_triangles _ _ _

end SerrePositivity.KST.SConstruction
