module
public import SerrePositivity.KST.Fibration.VerdierOriginalFullSCompositeVertices
public import SerrePositivity.KST.Fibration.VerdierNativeCompositeFunctoriality
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ControlledNativeTriangle

/-!
概要：動く上側終端の元の二短辺の標準合成二胞体と全 native Hom を構成する。
方針：同じ全 S• 合成実射の core 制限を元の同じ完全射へ厳密回収する。
規約：元の包含・商の合成端を保持し、新たな比較射を選ばない。
使われ方：K-6 c4 の上側終端の有限二胞体照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction SerrePositivity.KST.LocalizingInvariants

namespace SerrePositivity.KST.Fibration

/-- 概要：元の全 S• 合成実射の core 制限は元の同じ完全射の core 作用。
方針：同じ全 path 族の core 回収を合成 path 頂点で評価する。
規約：全射そのものの等式。使われ方：上側終端の標準合成 native Hom の照合。 -/
theorem verdierOriginalFullSCompositeMap_core (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) (j : Fin 2) :
    (show stableCoreSingleKanObject (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from d.left) ⟶
      fullSRealizationKanObject d.left from
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map (coreSFullRealizationInclusion (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from d.left))) ≫
      verdierOriginalFullSCompositeMap d j =
      (show stableCoreSingleKanObject (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from d.left) ⟶
        stableCoreSingleKanObject (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from d.right) from
          stableCoreSingleKanMap (verdierNullCompositeOriginalMap d j)) := by
  let p := (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map (coreSFullRealizationInclusion
    (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from d.left)))).app
      (stableCoreSingleKanObject (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from d.right)).obj
  apply (SimplicialCategory.homEquiv' (stableCoreSingleKanObject (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from d.left))
    (stableCoreSingleKanObject (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from d.right))).injective
  change p.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (show (fullSRealizationKanObject d.left).obj ⟶
    (stableCoreSingleKanObject (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from d.right)).obj from
      verdierOriginalFullSCompositeMap d j)) = _
  calc
    _ = p.app (Opposite.op ⦋0⦌) ((verdierOriginalFullSHomFamily d j).app (Opposite.op ⦋0⦌)
        (ComposableArrows.mk₀ coherentTriangleFullPath.{u})) :=
      congrArg (fun x => p.app (Opposite.op ⦋0⦌) x) (verdierOriginalFullSHomFamily_full d j).symm
    _ = (verdierOriginalNativeHomFamily d j).app (Opposite.op ⦋0⦌)
        (ComposableArrows.mk₀ coherentTriangleFullPath.{u}) :=
      congrArg (fun f => f.app (Opposite.op ⦋0⦌)
        (ComposableArrows.mk₀ coherentTriangleFullPath.{u})) (verdierOriginalFullSHomFamily_core d j)
    _ = _ := verdierOriginalNativeHomFamily_full d j

/-- 概要：元の core 包含と終端の全 S• 合成実射の標準合成二胞体。
方針：同じ二つの実 Kan 射へ正本の coherent 合成を適用する。
規約：元の二短辺を保持。使われ方：動く上側終端と同定する指定有限二胞体。 -/
def verdierMovingUpperLastTriangle (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveCompStruct (C := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u})
    (show stableCoreSingleKanObject (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from d.left) ⟶
      fullSRealizationKanObject d.left from
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map (coreSFullRealizationInclusion (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from d.left)))
    (verdierOriginalFullSCompositeMap d 1)

/-- 概要：同じ標準終端二胞体の全 native Hom は元の実合成端の定値全族。
方針：標準合成の native 定値回収と同じ実 core 制限を使う。
規約：元の全 path を保持。使われ方：再構成終端との full native Hom の照合。 -/
theorem verdierMovingUpperLastTriangle_native (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) :
    (SSet.uliftFunctor.{u + 1, u}).map
      ((verdierMovingUpperLastTriangle d).simplex.map ⟨ULift.up 0⟩ ⟨ULift.up 2⟩) =
      SSet.const (X := (SSet.uliftFunctor.{u + 1, u}).obj (nerve _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TriangleNativePath.{u}))
        (verdierNativeCompositePoint d 1) := by
  let f : stableCoreSingleKanObject (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from d.left) ⟶
      fullSRealizationKanObject d.left :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map (coreSFullRealizationInclusion (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from d.left))
  let g := verdierOriginalFullSCompositeMap d 1
  have hn : (verdierMovingUpperLastTriangle d).simplex.map ⟨ULift.up 0⟩ ⟨ULift.up 2⟩ =
      SSet.const (SimplicialCategory.homEquiv' (stableCoreSingleKanObject (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from d.left))
        (stableCoreSingleKanObject (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from d.right)) (f ≫ g)) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coherentNerveCompStruct_native_const f g
  have hp := congrArg (SimplicialCategory.homEquiv'
    (stableCoreSingleKanObject (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from d.left))
    (stableCoreSingleKanObject (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from d.right)))
    (verdierOriginalFullSCompositeMap_core d 1)
  have hc := congrArg (fun x => (SSet.uliftFunctor.{u + 1, u}).map
    (SSet.const (X := nerve _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TriangleNativePath.{u}) x)) hp
  exact (congrArg (fun k => (SSet.uliftFunctor.{u + 1, u}).map k) hn).trans
    (hc.trans (by
      apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro x
      rfl))

end SerrePositivity.KST.Fibration
