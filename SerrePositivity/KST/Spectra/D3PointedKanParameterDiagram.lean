module

public import SerrePositivity.KST.Spectra.D3PointedKanIhom
public import SerrePositivity.KST.Spectra.D3EnrichedOrderedDiagram

/-!
概要：パラメータ図式と点つき Kan 複体の全 Hom を同時に保持する実豊穣関手。
方針：順序円柱の各 Hom に同じパラメータ制限の混合 Hom を使う。
規約：パラメータの恒等・合成と全入力 Hom の恒等・合成を厳密に保持する。
使われ方：d3b② の元の端点円・path・零角を保つ全実図式族の構成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open SerrePositivity.InfinityCategories SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
open EnrichedOrderedCylinder
variable {J : Type v} [Preorder J] (D : Jᵒᵖ ⥤ PointedSimplicialSet.{u})

/-- 元の順序パラメータ図式が指定する、同じ逆向きの実射。 -/
def d3ParameterArrow {i j : J} (h : i ≤ j) : D.obj (Opposite.op j) ⟶ D.obj (Opposite.op i) :=
  D.map (homOfLE h).op

lemma d3ParameterArrow_id (i : J) : d3ParameterArrow D (le_rfl : i ≤ i) = 𝟙 _ :=
  D.map_id (Opposite.op i)

lemma d3ParameterArrow_comp {i j k : J} (h : i ≤ j) (h' : j ≤ k) :
    d3ParameterArrow D (le_trans h h') = d3ParameterArrow D h' ≫ d3ParameterArrow D h :=
  D.map_comp (homOfLE h').op (homOfLE h).op

/-- 元のパラメータ図式の各段の内部 Hom 豊穣関手。 -/
def d3ParameterStage (i : J) : EnrichedFunctor SSet.{u} PointedKanObject.{u} PointedKanObject.{u} :=
  d3PointedKanIhom (D.obj (Opposite.op i))

/-- 同じ元の逆向きパラメータ射が指定する混合 Hom。 -/
def d3ParameterMixed (i j : J) (h : i ≤ j) (X Y : PointedKanObject.{u}) :
    SimplicialCategory.sHom X Y ⟶
      SimplicialCategory.sHom ((d3ParameterStage D i).obj X) ((d3ParameterStage D j).obj Y) :=
  d3PointedKanMixed (d3ParameterArrow D h) X Y

lemma d3ParameterMixed_id (i : J) (X Y : PointedKanObject.{u}) :
    d3ParameterMixed D i i le_rfl X Y = (d3ParameterStage D i).map X Y := by
  dsimp only [d3ParameterMixed]
  rw [d3ParameterArrow_id, d3PointedKanMixed_id]
  rfl

lemma d3ParameterMixed_comp (i j k : J) (h : i ≤ j) (h' : j ≤ k)
    (X Y Z : PointedKanObject.{u}) :
    eComp SSet X Y Z ≫ d3ParameterMixed D i k (le_trans h h') X Z =
      (d3ParameterMixed D i j h X Y ⊗ₘ d3ParameterMixed D j k h' Y Z) ≫
        eComp SSet ((d3ParameterStage D i).obj X) ((d3ParameterStage D j).obj Y)
          ((d3ParameterStage D k).obj Z) := by
  dsimp only [d3ParameterMixed]
  rw [d3ParameterArrow_comp D h h']
  exact d3PointedKanMixed_comp _ _ X Y Z

/-- 全対象・全 Hom と元のパラメータ図式の同時評価を持つ実豊穣関手。 -/
def d3PointedKanParameterDiagram :
    EnrichedFunctor SSet.{u} (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedOrderedCylinder.Object J PointedKanObject.{u}) PointedKanObject.{u} :=
  D3EnrichedOrderedDiagram.functor (d3ParameterStage D) (d3ParameterMixed D)
    (d3ParameterMixed_id D) (d3ParameterMixed_comp D)

/-- 指定段への制限は、同じ元の内部 Hom 豊穣関手そのもの。 -/
lemma d3PointedKanParameterDiagram_stage (i : J) :
    (stageInclusion (C := PointedKanObject.{u}) i).comp SSet (d3PointedKanParameterDiagram D) =
      d3PointedKanIhom (D.obj (Opposite.op i)) :=
  D3EnrichedOrderedDiagram.stage _ _ _ _ i

end SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
