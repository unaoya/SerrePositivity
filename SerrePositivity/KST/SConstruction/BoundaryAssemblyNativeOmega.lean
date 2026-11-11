module
public import SerrePositivity.KST.SConstruction.PointedKanLoopInfinity
public import SerrePositivity.KST.SConstruction.BoundaryAssemblyOriginalCoherentDiagram

/-! # 実際の loop ∞ 関手を標的とする全入力 Ω 比較
概要：元の構造射を成分に持つ変換を、実際の loop ∞ 関手への Ω 比較として構成する。
方針：loop の strict 図式との全単体の等式を使い、元の円柱の射を保持して端点を照合する。
規約：別の変換を選び直さず、元の構造射の辺と図式全体の可逆性を保持する。
使われ方：元の K の段を、関手 ∞ 圏内の Ω 構造へ束ねる接続。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open Spectra
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 反復 S の loop 図式は、次段の全入力図式への実際の loop ∞ 関手の後合成。 -/
lemma boundaryKanLoopInfinity_diagram {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) :
    pointedKanCoherentDiagram (F ⋙ boundaryKanRealizationFunctor r)
        (fun i => boundaryKanRealization_kanComplex r (F.obj i)) ≫ pointedKanLoopInfinity =
      pointedKanCoherentDiagram (F ⋙ loopBoundaryKanFunctor r)
        (fun i => loopBoundaryKan_kanComplex r (F.obj i)) :=
  pointedKanLoopInfinity_diagram (F ⋙ boundaryKanRealizationFunctor r)
    (fun i => boundaryKanRealization_kanComplex r (F.obj i))

/-- 元の全入力円柱を保つ、実際の loop ∞ 関手への Ω 比較。 -/
def boundaryAssemblyNativeOmegaHomotopy {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) :
    SSet.Homotopy
      (pointedKanCoherentDiagram (F ⋙ boundaryKanRealizationFunctor r)
        (fun i => boundaryKanRealization_kanComplex r (F.obj i)))
      (pointedKanCoherentDiagram (F ⋙ boundaryKanRealizationFunctor (r + 1))
        (fun i => boundaryKanRealization_kanComplex (r + 1) (F.obj i)) ≫
          pointedKanLoopInfinity) where
  h := (boundaryAssemblyOriginalCoherentHomotopy r F).h
  h₀ := (boundaryAssemblyOriginalCoherentHomotopy r F).h₀
  h₁ := (boundaryAssemblyOriginalCoherentHomotopy r F).h₁.trans
    (boundaryKanLoopInfinity_diagram (r + 1) F).symm
  rel := (boundaryAssemblyOriginalCoherentHomotopy r F).rel

/-- Ω 比較の円柱の射は、元の全入力変換の円柱の射そのもの。 -/
lemma boundaryAssemblyNativeOmegaHomotopy_h {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) :
    (boundaryAssemblyNativeOmegaHomotopy r F).h =
      (boundaryAssemblyOriginalCoherentHomotopy r F).h := rfl

/-- 実際の loop ∞ 関手への比較も、元の固定構造射の辺を厳密に回収する。 -/
lemma boundaryAssemblyNativeOmegaHomotopy_vertex_edge {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) (i : I) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (boundaryAssemblyNativeOmegaHomotopy r F)
      (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex i))).edge =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (show (boundaryPointedKanDiagram r F).obj i ⟶
      (pointedKanDiagram (F ⋙ loopBoundaryKanFunctor (r + 1))
        (fun j => loopBoundaryKan_kanComplex (r + 1) (F.obj j))).obj i from
          ObjectProperty.homMk (boundaryKanAssemblyAdjoint r (F.obj i)))).edge :=
  boundaryAssemblyOriginalCoherentHomotopy_vertex_edge r F i

/-- 指定した元の全入力円柱は、実際の loop ∞ 関手への図式全体の Ω 同型。 -/
def boundaryAssemblyNativeOmegaIso {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (pointedKanCoherentDiagram (F ⋙ boundaryKanRealizationFunctor r)
        (fun i => boundaryKanRealization_kanComplex r (F.obj i)))
      (pointedKanCoherentDiagram (F ⋙ boundaryKanRealizationFunctor (r + 1))
        (fun i => boundaryKanRealization_kanComplex (r + 1) (F.obj i)) ≫
          pointedKanLoopInfinity) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.functorIsoOfPointwiseInvertibleHomotopy (boundaryAssemblyNativeOmegaHomotopy r F)
  rintro ⟨s⟩
  have hs : s = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (s.obj 0) := ComposableArrows.ext₀ rfl
  rw [hs]
  let f : (boundaryPointedKanDiagram r F).obj (s.obj 0) ⟶
      (pointedKanDiagram (F ⋙ loopBoundaryKanFunctor (r + 1))
        (fun j => loopBoundaryKan_kanComplex (r + 1) (F.obj j))).obj (s.obj 0) :=
    ObjectProperty.homMk (boundaryKanAssemblyAdjoint r (F.obj (s.obj 0)))
  have hf := pointedKanObject_edge_isInvertible_of_piIsomorphism f
    (boundaryKanAssemblyAdjoint_piIsomorphism r (F.obj (s.obj 0)))
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr
    (boundaryAssemblyNativeOmegaHomotopy_vertex_edge r F (s.obj 0)).symm).mp hf

end SerrePositivity.KST.SConstruction
