module
public import SerrePositivity.KST.SConstruction.KCompositionPrismSquares
public import SerrePositivity.KST.SConstruction.CoherentStrictPathEvaluation
public import SerrePositivity.KST.SConstruction.KPrismSliceDiagrams

/-! # 元の合成 prism の上下の strict 三角形の区間は定数
概要：上下面の元の二単体を同じ strict 図式へ戻し、その Hom 区間の定数性を証明する。
方針：元の prism の端点式と strict 図式の全 Path 評価の式を使う。
規約：定数性は元の区間について証明し、定数な別の代表を選ばない。
使われ方：元の合成三正方形の外側二辺を保持したまま縮約する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SimplicialThickening MonoidalCategory CartesianMonoidalCategory SSet
open Spectra Spectra.CoherentPathCoordinates SerrePositivity.InfinityCategories

open scoped Simplicial

/-- 元の strict 図式の三角形の Hom 区間は、元の長辺の頂点の定数族そのもの。 -/
lemma coherentTriangleTrace_strict {I : Type u} [SmallCategory I]
    {C : Type v} [Category.{u} C] [SimplicialCategory C] (F : I ⥤ C)
    (s : (nerve I) _⦋2⦌) :
    triangleTrace ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram F).app (Opposite.op ⦋2⦌) (ULift.up s)) =
      SSet.const (SimplicialCategory.homEquiv' _ _ (F.map (s.map (homOfLE (by decide :
        (0 : Fin 3) ≤ 2))))) := by
  change trianglePathInterval ≫ (coherentStringDiagramCell (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram F) s).map
    (.mk (ULift.up 0)) (.mk (ULift.up 2)) = _
  rw [coherentStringDiagramCell_strict_map F s 0 2 (by decide), SSet.comp_const]

local instance kCompositionPrismStrictFacesPointedCategory :
    SimplicialCategory PointedSimplicialSet.{u} := PointedEnrichment.simplicialCategory
variable {I : Type u} [SmallCategory I] (r : ℕ) (F : I ⥤ StableModel.{u})
  {x y z : I} (f : x ⟶ y) (g : y ⟶ z)

/-- 元の合成 prism の上面は、元の次段の strict 図式の同じ三角形。 -/
lemma kKanOriginalCompositionImage_top_strict :
    (SimplicialNerve PointedSimplicialSet.{u}).δ 0 (kKanOriginalCompositionImage r F f g 0) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram (F ⋙ kKanSequenceLevelFunctor (r + 1))).app (Opposite.op ⦋2⦌)
        (ULift.up (ComposableArrows.mk₂ f g)) := by
  have h := congrArg SSet.yonedaEquiv
    (kKanOriginalSuspensionPrism_one r F (ComposableArrows.mk₂ f g))
  simp only [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply] at h
  refine (trianglePrismImage_face (kKanOriginalCompositionPrism r F f g)
    trianglePrismTetrahedron_top).trans ?_
  exact h

/-- 元の合成 prism の下面は、元の段の suspension の strict 図式の同じ三角形。 -/
lemma kKanOriginalCompositionImage_bottom_strict :
    (SimplicialNerve PointedSimplicialSet.{u}).δ 3 (kKanOriginalCompositionImage r F f g 2) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram ((F ⋙ kKanSequenceLevelFunctor r) ⋙
        MonoidalCategory.tensorLeft PointedSimplicialSet.circle.{u})).app (Opposite.op ⦋2⦌)
        (ULift.up (ComposableArrows.mk₂ f g)) := by
  have h := kKanOriginalSuspensionPrism_zero r F (ComposableArrows.mk₂ f g)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.strictCoherentDiagram_postcomp, suspensionEnrichedUnderlying_eq] at h
  have hv := congrArg SSet.yonedaEquiv h
  simp only [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply] at hv
  refine (trianglePrismImage_face (kKanOriginalCompositionPrism r F f g)
    trianglePrismTetrahedron_bottom).trans ?_
  exact hv

/-- 上面の元の Hom 区間そのものは、全時刻で定数である。 -/
lemma kKanOriginalCompositionImage_top_trace_constant :
    ∃ v, triangleTrace ((SimplicialNerve PointedSimplicialSet.{u}).δ 0
      (kKanOriginalCompositionImage r F f g 0)) = SSet.const v := by
  apply (triangleTrace_constant_congr (kKanOriginalCompositionImage_top_strict r F f g)).mpr
  exact ⟨_, coherentTriangleTrace_strict _ _⟩

/-- 下面の元の Hom 区間そのものも、全時刻で定数である。 -/
lemma kKanOriginalCompositionImage_bottom_trace_constant :
    ∃ v, triangleTrace ((SimplicialNerve PointedSimplicialSet.{u}).δ 3
      (kKanOriginalCompositionImage r F f g 2)) = SSet.const v := by
  apply (triangleTrace_constant_congr (kKanOriginalCompositionImage_bottom_strict r F f g)).mpr
  exact ⟨_, coherentTriangleTrace_strict _ _⟩

end SerrePositivity.KST.SConstruction
