module
public import SerrePositivity.KST.SConstruction.EnrichedFunctorCollageCrossMaps
public import SerrePositivity.KST.Spectra.StrictDiagramTransformation

/-! # 上段への交差恒等射の全入力比較円柱
概要：strict な上段図式について、下段 R の像から上段そのものへの全入力変換を構成する。
方針：交差恒等射の通常の自然変換を実円柱にし、包含の全単体の後合成の式で端点を照合する。
規約：円柱の射を変えず、成分の辺は元の交差恒等射を厳密に回収する。
使われ方：元の Ω 比較を下段へ写した変換と、collage の ∞ 圏内で合成する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.InfinityCategories SerrePositivity.InfinityCategories.HomotopyLimits
open Spectra
variable {C D : Type v} [Category.{u} C] [Category.{u} D]
  [SimplicialCategory C] [SimplicialCategory D]
  {I : Type u} [SmallCategory I]

/-- 下段の R の像から上段へ、元の交差恒等射を持つ全入力円柱。 -/
def enrichedFunctorCollageComparisonHomotopy (R : EnrichedFunctor SSet.{u} C D)
    (G : I ⥤ C) : SSet.Homotopy
      (strictCoherentDiagram G ≫ coherentNerveMap R ≫ enrichedFunctorCollageBottomInfinity R)
      (strictCoherentDiagram G ≫ enrichedFunctorCollageTopInfinity R) := by
  let η := CategoryTheory.Functor.whiskerLeft G (enrichedFunctorCollageComparison R)
  let H := StrictDiagramTransformation.homotopy η
  have hs : strictCoherentDiagram G ≫ coherentNerveMap R ≫
      enrichedFunctorCollageBottomInfinity R =
    strictCoherentDiagram (G ⋙ (coherentEnrichedUnderlyingFunctor R ⋙
      coherentEnrichedUnderlyingFunctor (enrichedFunctorCollageBottom R))) := by
    rw [← Category.assoc, strictCoherentDiagram_postcomp]
    exact strictCoherentDiagram_postcomp (G ⋙ coherentEnrichedUnderlyingFunctor R)
      (enrichedFunctorCollageBottom R)
  have ht : strictCoherentDiagram G ≫ enrichedFunctorCollageTopInfinity R =
      strictCoherentDiagram (G ⋙ coherentEnrichedUnderlyingFunctor
        (enrichedFunctorCollageTop R)) :=
    strictCoherentDiagram_postcomp G (enrichedFunctorCollageTop R)
  refine { h := H.h, h₀ := H.h₀.trans hs.symm, h₁ := H.h₁.trans ht.symm, rel := ?_ }
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro x
  exact False.elim x.1.property

/-- 全入力の比較は元の自然変換の円柱の射を保持する。 -/
lemma enrichedFunctorCollageComparisonHomotopy_h (R : EnrichedFunctor SSet.{u} C D)
    (G : I ⥤ C) :
    (enrichedFunctorCollageComparisonHomotopy R G).h =
      (StrictDiagramTransformation.homotopy
        (CategoryTheory.Functor.whiskerLeft G (enrichedFunctorCollageComparison R))).h := rfl

/-- 全入力比較の対象での辺は、元の交差恒等射の coherent な辺そのもの。 -/
lemma enrichedFunctorCollageComparisonHomotopy_vertex_edge
    (R : EnrichedFunctor SSet.{u} C D) (G : I ⥤ C) (i : I) :
    (simplicialHomotopyVertexEdge (enrichedFunctorCollageComparisonHomotopy R G)
      (ULift.up (nerveVertex i))).edge =
      (coherentNerveEdge (enrichedFunctorCollageCross R (𝟙 (R.obj (G.obj i))))).edge :=
  StrictDiagramTransformation.component_edge
    (CategoryTheory.Functor.whiskerLeft G (enrichedFunctorCollageComparison R)) i

end SerrePositivity.KST.SConstruction
