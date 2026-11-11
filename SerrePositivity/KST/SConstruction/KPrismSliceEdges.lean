module
public import SerrePositivity.KST.SConstruction.KPrismSliceDiagrams
public import SerrePositivity.KST.SConstruction.CoherentPrismNativeFamilies

/-! # 元の K prism の水平辺と縦辺を回収する
概要：通常積圏表示の水平辺と縦辺が、元の段の射と構造射の辺そのものであることを証明する。
方針：両端の図式の厳密な回収と、元の円柱の指定成分の辺の等式を用いる。
規約：零段を含む全段で元の辺を保持する。
使われ方：上下の合成列族の終点を、元の二合成へ同定する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open Spectra SerrePositivity.InfinityCategories
open scoped Simplicial
local instance kPrismSliceEdges_pointed_simplicialCategory :
    SimplicialCategory PointedSimplicialSet.{u} := PointedEnrichment.simplicialCategory

/-- 下段の元の辺は、元の段の写像の suspension の辺そのもの。 -/
lemma kKanOriginalPrismStringEdge_bottom {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {x y : I} (f : x ⟶ y) :
    (kKanOriginalPrismStringDiagram r F).app (Opposite.op ⦋1⦌)
      (ULift.up (nerve.edgeMk ((coherentPrismSliceFunctor I (ULift.up 0)).map f)).edge) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (((F ⋙ kKanSequenceLevelFunctor r) ⋙
        MonoidalCategory.tensorLeft PointedSimplicialSet.circle.{u}).map f)).edge := by
  have h := congrArg (fun Q => Q.app (Opposite.op ⦋1⦌)
    (ULift.up (nerve.edgeMk f).edge)) (kKanOriginalPrismStringDiagram_bottom r F)
  change (kKanOriginalPrismStringDiagram r F).app _ (ULift.up
    ((nerveMap (coherentPrismSliceFunctor I (ULift.up 0))).app _ (nerve.edgeMk f).edge)) = _ at h
  rw [nerve.edgeMk_edge, nerveMap_app_mk₁] at h
  exact h.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictCoherentDiagram_edge _ f)

/-- 上段の元の辺は、元の次段の写像の辺そのもの。 -/
lemma kKanOriginalPrismStringEdge_top {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {x y : I} (f : x ⟶ y) :
    (kKanOriginalPrismStringDiagram r F).app (Opposite.op ⦋1⦌)
      (ULift.up (nerve.edgeMk ((coherentPrismSliceFunctor I (ULift.up 1)).map f)).edge) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge ((F ⋙ kKanSequenceLevelFunctor (r + 1)).map f)).edge := by
  have h := congrArg (fun Q => Q.app (Opposite.op ⦋1⦌)
    (ULift.up (nerve.edgeMk f).edge)) (kKanOriginalPrismStringDiagram_top r F)
  change (kKanOriginalPrismStringDiagram r F).app _ (ULift.up
    ((nerveMap (coherentPrismSliceFunctor I (ULift.up 1))).app _ (nerve.edgeMk f).edge)) = _ at h
  rw [nerve.edgeMk_edge, nerveMap_app_mk₁] at h
  exact h.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictCoherentDiagram_edge _ f)

/-- 積圏表示の元の縦辺は、元の K の同じ構造射の指定辺そのもの。 -/
lemma kKanOriginalPrismStringEdge_vertical {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) (i : I) :
    (kKanOriginalPrismStringDiagram r F).app (Opposite.op ⦋1⦌)
      (ULift.up (nerve.edgeMk (coherentPrismArrow (𝟙 i))).edge) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge ((kKanSequence (F.obj i)).sigma r)).edge := by
  have hp : (coherentOrdinaryPrismIso.{u, u + 1} I).hom.app (Opposite.op ⦋1⦌)
      (ULift.up (nerve.edgeMk (coherentPrismArrow (𝟙 i))).edge) =
      (((SSet.uliftFunctor.{u + 1, u}).obj (nerve I)).map (SimplexCategory.σ 0).op
        (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex i)), SSet.stdSimplex.objEquiv.symm (𝟙 ⦋1⦌)) := by
    apply Prod.ext
    · apply ULift.ext
      refine ComposableArrows.ext₁ ?_ ?_ ?_
      · rfl
      · rfl
      · simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
        rfl
    · apply SSet.stdSimplex.ext
      intro j
      fin_cases j <;> rfl
  have h := kKanOriginalSuspensionHomotopy_vertex_edge F r i
  change (kKanOriginalSuspensionHomotopy F r).h.app (Opposite.op ⦋1⦌) _ = _ at h
  change (kKanOriginalSuspensionHomotopy F r).h.app _
    ((coherentOrdinaryPrismIso.{u, u + 1} I).hom.app _
      (ULift.up (nerve.edgeMk (coherentPrismArrow (𝟙 i))).edge)) = _
  rw [hp]
  refine (congrArg ((kKanOriginalSuspensionHomotopy F r).h.app (Opposite.op ⦋1⦌)) ?_).trans h
  apply Prod.ext
  · rfl
  · apply SSet.stdSimplex.ext
    intro j
    fin_cases j <;> rfl

end SerrePositivity.KST.SConstruction
