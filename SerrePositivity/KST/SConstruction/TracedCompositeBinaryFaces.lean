module
public import SerrePositivity.KST.SConstruction.TracedCompositeBinaryTriangle

/-! # 元の合成補正の実三角形の三つの全 raw 辺
概要：実二部分三角形の三辺を、元の二本の単一射補正と元の段三角形の合成辺へ照合する。
方針：同じ全円柱の唯一の一点での評価を回収し、元の全区間写像の式を使う。
規約：辺の全一単体を保持し、元の三円柱の代表を選び直さない。
使われ方：三入力の外側二面の合成補正辺を、元の単一射補正・実交換面へ接続する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet Spectra
open SerrePositivity.InfinityCategories
open scoped Simplicial
variable {I : Type u} [SmallCategory I] (F : I ⥤ StableModel.{u})
  {x y z : I} (f : x ⟶ y) (g : y ⟶ z)

/-- 第一辺全体は、元の前の単一射補正の同じ後合成像。 -/
lemma monicKPrismCompositeBinaryPointTriangle_first (n : ℕ) :
    stdSimplex.δ 2 ≫
        SSet.yonedaEquiv.symm (monicKPrismCompositeBinaryPointTriangle F f g n).simplex =
      monicKTracedUnaryCorrectionAtPoint F f n ≫
        (PointedObject.basedHomMap ((kOmegaSpectrum (F.obj x)).level n).space
          (kKanSequenceLevelMap (F.map g) n)).right := by
  rw [SSet.Edge.CompStruct.δ_two_yonedaEquiv_symm]
  change SSet.yonedaEquiv.symm
    (pointFamilyHomotopyEdge (monicKPrismCompositePointFirstData F f g n).homotopy).edge = _
  rw [pointFamilyHomotopyEdge_map, monicKPrismCompositePointFirstData_h]
  change intervalParameterPoint (SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u}))) ≫
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint (coherentArrowStringDirect f) ▷ (Δ[1] : SSet.{u})) ≫
      (monicKPrismUnaryCorrectionData F f n).homotopy.h) ≫ _ = _
  simp only [← Category.assoc]
  rw [intervalParameterPoint, intervalParameterPoint_of_map]
  rfl

/-- 第二辺全体も、元の後の単一射補正と同じ第一 BF 段頂点の実合成像。 -/
lemma monicKPrismCompositeBinaryPointTriangle_second (n : ℕ) :
    stdSimplex.δ 0 ≫
        SSet.yonedaEquiv.symm (monicKPrismCompositeBinaryPointTriangle F f g n).simplex =
      monicKTracedUnaryCorrectionAtPoint F g n ≫ monicKTracedTripleLastPairStageMap F f z n := by
  rw [SSet.Edge.CompStruct.δ_zero_yonedaEquiv_symm]
  change SSet.yonedaEquiv.symm
    (pointFamilyHomotopyEdge (monicKPrismCompositePointSecondData F f g n).homotopy).edge = _
  rw [pointFamilyHomotopyEdge_map, monicKPrismCompositePointSecondData_h]
  change intervalParameterPoint (SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u}))) ≫
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint (coherentArrowStringDirect g) ▷ (Δ[1] : SSet.{u})) ≫
      (monicKPrismUnaryCorrectionData F g n).homotopy.h) ≫ _ = _
  simp only [← Category.assoc]
  rw [intervalParameterPoint, intervalParameterPoint_of_map]
  rfl

/-- 対角辺全体は、元の BF 段三角形の同じ合成補正辺そのもの。 -/
lemma monicKPrismCompositeBinaryPointTriangle_direct (n : ℕ) :
    stdSimplex.δ 1 ≫
        SSet.yonedaEquiv.symm (monicKPrismCompositeBinaryPointTriangle F f g n).simplex =
      SSet.yonedaEquiv.symm (monicKTracedCompositionStageTriangleData F f g n).direct.edge := by
  rw [SSet.Edge.CompStruct.δ_one_yonedaEquiv_symm]
  change SSet.yonedaEquiv.symm
    (pointFamilyHomotopyEdge (monicKPrismCompositeConstantPointData F f g n).homotopy).edge = _
  rw [pointFamilyHomotopyEdge_map, monicKPrismCompositeConstantPointData_h,
    monicKPrismCompositePointData_h]
  change intervalParameterPoint (SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u}))) ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint (compositionStringDirect f g) ▷ (Δ[1] : SSet.{u})) ≫ _ = _
  rw [← Category.assoc, intervalParameterPoint, intervalParameterPoint_of_map]
  exact (monicKTracedCompositionStageTriangleData_direct F f g n).symm

/-- 左外側の第二全補正辺は、元の同じ実交換三角形対の第一下辺。 -/
lemma monicKPrismCompositeBinaryPointTriangle_second_interchange
    {t : I} (h : z ⟶ t) (n : ℕ) :
    stdSimplex.δ 0 ≫
        SSet.yonedaEquiv.symm (monicKPrismCompositeBinaryPointTriangle F (f ≫ g) h n).simplex =
      SSet.yonedaEquiv.symm (monicKTracedTripleInterchangeFirstLower F f g h n).edge := by
  rw [monicKPrismCompositeBinaryPointTriangle_second, monicKTracedTripleInterchangeFirstLower_map]
  exact pointedFixedLeftVertexComposition_apply (monicKTracedBFStageVertex F (f ≫ g) n)
    (monicKTracedUnaryCorrectionAtPoint F h n)

end SerrePositivity.KST.SConstruction
