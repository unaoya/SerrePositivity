module
public import SerrePositivity.KST.SConstruction.CoherentHomotopyComponentCalculus
public import SerrePositivity.KST.SConstruction.EnrichedCollageTransport
public import SerrePositivity.KST.SConstruction.HomotopySpecifiedVertexCorrection

/-! # Collage 内の合成した円柱の成分
概要：合成した円柱の各成分の射の類を、元の指定した交差射の類と照合する。
方針：全体三角形を評価し、下段射と交差恒等射の通常の合成三角形と比較する。
規約：元の入力円柱の指定成分と全体の指定三角形を使用する。
使われ方：全対象で固定構造射を厳密に回収する円柱の補正。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial
variable {C D : Type v} [Category.{u} C] [Category.{u} D]
  [SimplicialCategory C] [SimplicialCategory D]
  {I : Type u} [SmallCategory I]

/-- 元の射を、下段と上段の元の図式の頂点を端点とする交差辺として読む。 -/
def enrichedFunctorCollageCrossVertexEdge (R : EnrichedFunctor SSet.{u} C D)
    (F : I ⥤ D) (G : I ⥤ C) (i : I) (f : F.obj i ⟶ R.obj (G.obj i)) :
    (EnrichedFunctorCollageInfinity R).Edge
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram F ≫ enrichedFunctorCollageBottomInfinity R).app
        (Opposite.op ⦋0⦌) (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex i)))
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram G ≫ enrichedFunctorCollageTopInfinity R).app
        (Opposite.op ⦋0⦌) (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex i))) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (enrichedFunctorCollageCross R f)).ofEq
    (strictCoherentDiagram_postcomp_vertex F (enrichedFunctorCollageBottom R) i).symm
    (strictCoherentDiagram_postcomp_vertex G (enrichedFunctorCollageTop R) i).symm

/-- 合成した円柱の成分は、元の指定した射の交差辺と同じ射の類を持つ。 -/
lemma enrichedFunctorCollageTransport_vertex_hom (R : EnrichedFunctor SSet.{u} C D)
    [Quasicategory (EnrichedFunctorCollageInfinity R)]
    {F : I ⥤ D} {G : I ⥤ C}
    (H : SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram F)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram G ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap R))
    (i : I) (f : F.obj i ⟶ R.obj (G.obj i))
    (hf : (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex i))).edge =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f).edge) :
    SSet.Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (enrichedFunctorCollageTransportHomotopy R H)
        (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex i))).toTruncated =
      SSet.Truncated.HomotopyCategory.homMk
        (enrichedFunctorCollageCrossVertexEdge R F G i f).toTruncated := by
  let a := ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex i)
  let l := enrichedFunctorCollageInputHomotopy R H
  let r := enrichedFunctorCollageComparisonHomotopy R G
  have hl : (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge l a).edge =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor
        (enrichedFunctorCollageBottom R)).map f)).edge := by
    exact (homotopyVertexEdge_postcomp H (enrichedFunctorCollageBottomInfinity R) a).trans
      ((congrArg ((enrichedFunctorCollageBottomInfinity R).app (Opposite.op ⦋1⦌)) hf).trans
        (enrichedNerveMap_edge (enrichedFunctorCollageBottom R) f))
  have hr := enrichedFunctorCollageComparisonHomotopy_vertex_edge R G i
  have hc : SSet.Edge.CompStruct (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge l a)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge r a) (enrichedFunctorCollageCrossVertexEdge R F G i f) := by
    refine (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveCompStruct
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor (enrichedFunctorCollageBottom R)).map f)
      (enrichedFunctorCollageCross R (𝟙 (R.obj (G.obj i))))).ofEq hl.symm hr.symm ?_
    rw [enrichedFunctorCollageCross_pre, Category.comp_id]
    rfl
  exact (homotopyCompositionTriangle_vertex_hom l r _
    (enrichedFunctorCollageTransportTriangle R H) a).symm.trans
      (SSet.Truncated.HomotopyCategory.homMk_comp_homMk hc.toTruncated)

/-- 元の全対象の指定射を交差辺として厳密に持ち、合成した全体の射の類を保つ補正。 -/
lemma exists_enrichedFunctorCollageTransport_specified_components
    (R : EnrichedFunctor SSet.{u} C D)
    [Quasicategory (EnrichedFunctorCollageInfinity R)]
    {F : I ⥤ D} {G : I ⥤ C}
    (H : SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram F)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram G ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap R))
    (f : ∀ i, F.obj i ⟶ R.obj (G.obj i))
    (hf : ∀ i, (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex i))).edge =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (f i)).edge) :
    ∃ H' : SSet.Homotopy
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram F ≫ enrichedFunctorCollageBottomInfinity R)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram G ≫ enrichedFunctorCollageTopInfinity R),
      (∀ i, (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H' (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex i))).edge =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (enrichedFunctorCollageCross R (f i))).edge) ∧
      SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H') =
        SSet.Truncated.HomotopyCategory.homMk
          (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (enrichedFunctorCollageTransportHomotopy R H)) := by
  let e : ∀ a : ((SSet.uliftFunctor.{v,u}).obj (nerve I)) _⦋0⦌,
      (EnrichedFunctorCollageInfinity R).Edge
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram F ≫ enrichedFunctorCollageBottomInfinity R).app
          (Opposite.op ⦋0⦌) a)
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram G ≫ enrichedFunctorCollageTopInfinity R).app
          (Opposite.op ⦋0⦌) a) := by
    rintro ⟨a⟩
    have ha : a = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (a.obj 0) := ComposableArrows.ext₀ rfl
    exact (enrichedFunctorCollageCrossVertexEdge R F G (a.obj 0) (f (a.obj 0))).ofEq
      (congrArg ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram F ≫ enrichedFunctorCollageBottomInfinity R).app
        (Opposite.op ⦋0⦌)) (congrArg ULift.up ha)).symm
      (congrArg ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram G ≫ enrichedFunctorCollageTopInfinity R).app
        (Opposite.op ⦋0⦌)) (congrArg ULift.up ha)).symm
  obtain ⟨H', he, hh⟩ := exists_homotopy_specified_vertex_edges
    (enrichedFunctorCollageTransportHomotopy R H) e (by
      rintro ⟨a⟩
      obtain ⟨i, rfl⟩ : ∃ i, a = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex i := ⟨a.obj 0, ComposableArrows.ext₀ rfl⟩
      exact enrichedFunctorCollageTransport_vertex_hom R H i (f i) (hf i))
  exact ⟨H', fun i => he (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex i)), hh⟩

end SerrePositivity.KST.SConstruction
