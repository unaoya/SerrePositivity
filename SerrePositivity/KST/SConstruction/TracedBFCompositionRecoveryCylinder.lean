module
public import SerrePositivity.KST.SConstruction.TracedBFCompositionRecovery
public import SerrePositivity.KST.SConstruction.EndpointFixedDiamondComparison

/-! # 元の BF 比較辺と復号辺の全端点固定直接比較円柱
概要：元の BF 比較辺と保存した合成面の復号辺を、両端を全時刻固定する実円柱で結ぶ。
方針：保存した同じ二実三角形の正方形を固定境界 Kan 写像空間の外側ホーンとして貼る。
規約：元の二円柱・両実三角形全体を同じ高次比較の面として厳密に回収する。
使われ方：三入力の生成面・指定面の比較を元の BF 比較と raw 高次 prism へ接続する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet Spectra
open scoped Simplicial
local instance tracedRecoveryCylinderSpectrumSimplicialCategory :
    SimplicialCategory OmegaSpectrum.{u} := OmegaSpectrum.simplicialCategory
local instance tracedRecoveryCylinderMappingKan (A B : OmegaSpectrum.{u}) :
    KanComplex (SimplicialCategory.sHom A B) := OmegaSpectrum.mappingSpace_kanComplex A B
variable {I : Type u} [SmallCategory I] (F : I ⥤ StableModel.{u})
  {x y z : I} (f : x ⟶ y) (g : y ⟶ z)

/-- 元の BF 比較辺と復号辺を直接結び、元の両円柱を面に保持する境界固定比較データ。 -/
def monicKTracedCompositionRecoveryCylinderData :=
  endpointFixedDiamondComparisonData (monicKTracedCompositionRecovery F f g)

/-- 元の同じ BF 辺から保存した同じ合成面の全復号辺への、両端固定の直接比較円柱。 -/
def monicKTracedCompositionRecoveryCylinder : SSet.Homotopy
    (SSet.yonedaEquiv.symm (monicKTracedSpectrumCompositionEdge F f g).edge)
    (SSet.yonedaEquiv.symm (coherentTriangleMappingEdge (monicKTracedSpectrumMap F f)
      (monicKTracedSpectrumMap F g) (monicKTracedSpectrumMap F (f ≫ g))
      (monicKTracedCoherentComposition F f g)).edge) :=
  (monicKTracedCompositionRecoveryCylinderData F f g).homotopy

/-- 元の全区間境界を、全比較時刻で厳密に固定する。 -/
lemma monicKTracedCompositionRecoveryCylinder_relative :
    ((SSet.boundary 1).ι ▷ (Δ[1] : SSet.{u})) ≫
        (monicKTracedCompositionRecoveryCylinder F f g).h =
      fst (SSet.boundary 1).toSSet Δ[1] ≫ (SSet.boundary 1).ι ≫
        SSet.yonedaEquiv.symm (monicKTracedSpectrumCompositionEdge F f g).edge :=
  (monicKTracedCompositionRecoveryCylinderData F f g).relative

/-- 元の二つの全円柱と直接比較円柱を同時に保持する、同じ高次比較の実写像。 -/
def monicKTracedCompositionRecoveryCylinderRealization :=
  endpointFixedDiamondComparisonRealization (monicKTracedCompositionRecovery F f g)

/-- 元の両円柱を保持する高次比較全体も、全パラメータで元の全区間境界を固定する。 -/
lemma monicKTracedCompositionRecoveryCylinderRealization_relative :
    ((SSet.boundary 1).ι ▷ (Δ[2] : SSet.{u})) ≫
        monicKTracedCompositionRecoveryCylinderRealization F f g =
      fst (SSet.boundary 1).toSSet Δ[2] ≫ (SSet.boundary 1).ι ≫
        SSet.yonedaEquiv.symm (monicKTracedSpectrumCompositionEdge F f g).edge :=
  endpointFixedDiamondComparisonRealization_relative _

/-- 直接比較面は元の両 BF 辺を両端に持つ同じ比較円柱全体。 -/
lemma monicKTracedCompositionRecoveryCylinderRealization_comparison :
    ((Δ[1] : SSet.{u}) ◁ stdSimplex.δ 2) ≫
        monicKTracedCompositionRecoveryCylinderRealization F f g =
      (monicKTracedCompositionRecoveryCylinder F f g).h :=
  endpointFixedDiamondComparisonRealization_comparison _

/-- 第一の元の全円柱は、同じ高次比較の合成面として厳密に回収する。 -/
lemma monicKTracedCompositionRecoveryCylinderRealization_first :
    ((Δ[1] : SSet.{u}) ◁ stdSimplex.δ 1) ≫
        monicKTracedCompositionRecoveryCylinderRealization F f g =
      (endpointFixedTriangleHomotopy (monicKTracedCompositionRecovery F f g).first).h :=
  endpointFixedDiamondComparisonRealization_first _

/-- 第二の元の全円柱も、同じ高次比較の第二面として厳密に回収する。 -/
lemma monicKTracedCompositionRecoveryCylinderRealization_second :
    ((Δ[1] : SSet.{u}) ◁ stdSimplex.δ 0) ≫
        monicKTracedCompositionRecoveryCylinderRealization F f g =
      (endpointFixedTriangleHomotopy (monicKTracedCompositionRecovery F f g).second).h :=
  endpointFixedDiamondComparisonRealization_second _

/-- 第一の元の実比較三角形全体も、同じ高次比較の指定面として保持する。 -/
lemma monicKTracedCompositionRecoveryCylinderRealization_first_triangle :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.lower ≫ ((Δ[1] : SSet.{u}) ◁ stdSimplex.δ 1) ≫
        monicKTracedCompositionRecoveryCylinderRealization F f g =
      SSet.yonedaEquiv.symm (monicKTracedCompositionRecovery F f g).first.simplex :=
  endpointFixedDiamondComparisonRealization_first_triangle _

/-- 第二の元の実比較三角形全体も、同じ高次比較の指定面として保持する。 -/
lemma monicKTracedCompositionRecoveryCylinderRealization_second_triangle :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.lower ≫ ((Δ[1] : SSet.{u}) ◁ stdSimplex.δ 0) ≫
        monicKTracedCompositionRecoveryCylinderRealization F f g =
      SSet.yonedaEquiv.symm (monicKTracedCompositionRecovery F f g).second.simplex :=
  endpointFixedDiamondComparisonRealization_second_triangle _

end SerrePositivity.KST.SConstruction
