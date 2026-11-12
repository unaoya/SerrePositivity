module
public import SerrePositivity.KST.SConstruction.KOriginalSuspensionPrisms
public import SerrePositivity.KST.SConstruction.SquareBoundaryEdgeCalculus

/-! # 元の K の全段の自然性 square の実三角形の復号
概要：零段を含む全段で、元の段の射と固定構造射の square の二つの三角形を回収する。
方針：元の全入力 prism の四辺を計算し、その同じ二つの標準三角形を復号する。
規約：元の Kan 列と元の構造射を保持し、全点つき対象の局所 Kan 性は使わない。
使われ方：元の適合ホモトピーと、パラメータ付き相対厳密化への接続。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open Spectra
open SerrePositivity.InfinityCategories
open scoped Simplicial
local instance kSuspensionMappingTriangles_pointed_simplicialCategory :
    SimplicialCategory PointedSimplicialSet.{u} := PointedEnrichment.simplicialCategory

/-- 元の K の全段の固定構造射に対する、同じ全入力 prism の自然性 square。 -/
def kKanOriginalSuspensionSquare {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {i j : I} (f : i ⟶ j) :
    (Δ[1] : SSet.{u + 1}) ⊗ Δ[1] ⟶ SimplicialNerve PointedSimplicialSet.{u} :=
  kKanOriginalSuspensionPrism r F (nerve.edgeMk f).edge

/-- 全段の square の下辺は元の各段の入力射の suspension。 -/
lemma kKanOriginalSuspensionSquare_zero {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {i j : I} (f : i ⟶ j) :
    SSet.ι₀ ≫ kKanOriginalSuspensionSquare r F f =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge
        (PointedSimplicialSet.circle.{u} ◁ kKanSequenceLevelMap (F.map f) r)).edge := by
  cases r with
  | zero =>
    rw [kKanOriginalSuspensionSquare, kKanOriginalSuspensionPrism_zero,
      ← Category.assoc, SSet.yonedaEquiv_symm_comp,
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictCoherentDiagram_edge (F ⋙ kKanSequenceLevelFunctor 0) f,
      SSet.yonedaEquiv_symm_comp, enrichedNerveMap_edge, suspensionEnrichedUnderlying_map]
    rfl
  | succ r => exact boundaryAssemblyOriginalSuspensionSquare_zero r F f

/-- 全段の square の上辺は元の次段の入力射。 -/
lemma kKanOriginalSuspensionSquare_one {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {i j : I} (f : i ⟶ j) :
    SSet.ι₁ ≫ kKanOriginalSuspensionSquare r F f =
      SSet.yonedaEquiv.symm
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (kKanSequenceLevelMap (F.map f) (r + 1))).edge := by
  cases r with
  | zero =>
    rw [kKanOriginalSuspensionSquare, kKanOriginalSuspensionPrism_one,
      SSet.yonedaEquiv_symm_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictCoherentDiagram_edge (F ⋙ kKanSequenceLevelFunctor 1) f]
    rfl
  | succ r => exact boundaryAssemblyOriginalSuspensionSquare_one r F f

/-- 全段の square の左辺は元の始点の固定構造射。 -/
lemma kKanOriginalSuspensionSquare_left {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {i j : I} (f : i ⟶ j) :
    lift (SSet.const (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 2)))
      (𝟙 (Δ[1] : SSet.{u + 1})) ≫ kKanOriginalSuspensionSquare r F f =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge ((kKanSequence (F.obj i)).sigma r)).edge :=
  kKanOriginalSuspensionPrism_vertex r F (nerve.edgeMk f).edge (SSet.stdSimplex.obj₀Equiv.symm 0)

/-- 全段の square の右辺は元の終点の固定構造射。 -/
lemma kKanOriginalSuspensionSquare_right {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {i j : I} (f : i ⟶ j) :
    lift (SSet.const (SSet.stdSimplex.obj₀Equiv.symm (1 : Fin 2)))
      (𝟙 (Δ[1] : SSet.{u + 1})) ≫ kKanOriginalSuspensionSquare r F f =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge ((kKanSequence (F.obj j)).sigma r)).edge :=
  kKanOriginalSuspensionPrism_vertex r F (nerve.edgeMk f).edge (SSet.stdSimplex.obj₀Equiv.symm 1)

/-- 元の全段の square の共通対角射と、元の四辺を保持した二つの実三角形。 -/
def kKanSuspensionMappingTriangles {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {i j : I} (f : i ⟶ j) :
    CoherentSquareMappingTriangles
      (PointedSimplicialSet.circle.{u} ◁ kKanSequenceLevelMap (F.map f) r)
      (kKanSequenceLevelMap (F.map f) (r + 1))
      ((kKanSequence (F.obj i)).sigma r) ((kKanSequence (F.obj j)).sigma r) :=
  coherentSquareMappingTrianglesOfBoundary _ _ _ _ (kKanOriginalSuspensionSquare r F f)
    (kKanOriginalSuspensionSquare_zero r F f) (kKanOriginalSuspensionSquare_one r F f)
    (kKanOriginalSuspensionSquare_left r F f) (kKanOriginalSuspensionSquare_right r F f)

end SerrePositivity.KST.SConstruction
