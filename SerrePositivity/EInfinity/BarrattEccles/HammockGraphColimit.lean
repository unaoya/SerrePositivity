module

public import SerrePositivity.EInfinity.BarrattEccles.HammockGraphTransition
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColimitGraph

/-!
# 元の E 代数の全語の hammock graph の余極限

概要：任意の可換環上で、同じ元の全語の図式・余極限・Map^h からの比較を構成。
方針：実際の弱同値に全語の図式を代入し、三列の比較へ元の標準射を合成する。
規約：三列から余極限への弱同値性は後続。元の Map^h の共通始域を保持する。
使われ方：hammock と既存 DK Hom の高次比較。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory HomotopicalAlgebra Opposite
open SerrePositivity.SimplicialModel

namespace SerrePositivity.EInfinity.BarrattEccles

variable (A : Type u) [CommRing A]

/-- 同じ実際の E 代数の全語の graph の厳密な図式。 -/
def algebraHammockGraphDiagram (X Y : (operad A).Algebra) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word ⥤ SSet.{u + 1} := by
  let := modelCategory A
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram (weakEquivalences (operad A).Algebra) X Y

@[simp] lemma algebraHammockGraphDiagram_obj (X Y : (operad A).Algebra) (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) :
    (algebraHammockGraphDiagram A X Y).obj w = algebraHammockGraph A w X Y := rfl

lemma algebraHammockGraphDiagram_map (X Y : (operad A).Algebra)
    {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} (f : a ⟶ b) :
    (algebraHammockGraphDiagram A X Y).map f = algebraHammockGraphMap A f X Y := rfl

/-- 元の全語の graph の単体集合としての余極限。 -/
def algebraHammockColimitGraph (X Y : (operad A).Algebra) : SSet.{u + 1} := by
  let := modelCategory A
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph (weakEquivalences (operad A).Algebra) X Y

/-- 同じ固定語の元の標準射。 -/
def algebraHammockGraphInclusion (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (X Y : (operad A).Algebra) :
    algebraHammockGraph A w X Y ⟶ algebraHammockColimitGraph A X Y := by
  let := modelCategory A
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion (weakEquivalences (operad A).Algebra) X Y w

/-- 元の列の圧縮と空列の挿入は、同じ余極限の標準射と可換。 -/
lemma algebraHammockGraphInclusion_naturality (X Y : (operad A).Algebra)
    {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} (f : a ⟶ b) :
    algebraHammockGraphMap A f X Y ≫ algebraHammockGraphInclusion A b X Y =
      algebraHammockGraphInclusion A a X Y := by
  let := modelCategory A
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion_naturality (weakEquivalences (operad A).Algebra) X Y f

/-- 元の全語の図式と同じ標準射を使う実際の余錐。 -/
def algebraHammockGraphCocone (X Y : (operad A).Algebra) :
    Limits.Cocone (algebraHammockGraphDiagram A X Y) :=
  { pt := algebraHammockColimitGraph A X Y
    ι :=
      { app w := algebraHammockGraphInclusion A w X Y
        naturality _ _ f := (algebraHammockGraphInclusion_naturality A X Y f).trans
          (Category.comp_id _).symm } }

/-- 同じ元の余錐は、単体集合の圏で実際に余極限となる。 -/
def algebraHammockGraphCocone_isColimit (X Y : (operad A).Algebra) :
    Limits.IsColimit (algebraHammockGraphCocone A X Y) := by
  let := modelCategory A
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph_isColimit (weakEquivalences (operad A).Algebra) X Y

/-- 同じ元の共通始域から全語の graph の余極限へ入れる射。 -/
def mappingSpaceHammockColimitNerveMap (X Y : (operad A).Algebra) :
    nerve (ULiftHom.{u + 1} (((((mappingSpace A).obj (op X)).obj Y).Elements)ᵒᵖ)) ⟶
      algebraHammockColimitGraph A X Y :=
  mappingSpaceHammockGraphNerveMap A X Y ≫
    algebraHammockGraphInclusion A _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.threeArrow X Y

/-- 同じ元の三列の比較を用いた、局所化後の全語の余極限への比較。 -/
def mappingSpaceHammockColimitComparison (X Y : (operad A).Algebra) :
    AnodyneHomotopy.anodyneQ.obj
        (SSet.uliftFunctor.{u + 1, u}.obj (((mappingSpace A).obj (op X)).obj Y)) ⟶
      AnodyneHomotopy.anodyneQ.obj (algebraHammockColimitGraph A X Y) :=
  (mappingSpaceHammockGraphComparisonIso A X Y).hom ≫
    AnodyneHomotopy.anodyneQ.map
      (algebraHammockGraphInclusion A _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.threeArrow X Y)

/-- 元の左射の後の比較は、同じ元の全語の余極限への右射を厳密に回収。 -/
lemma mappingSpaceHammockColimitComparison_fac (X Y : (operad A).Algebra) :
    AnodyneHomotopy.anodyneQ.map (mappingSpaceIndexAugmentation A X Y) ≫
        mappingSpaceHammockColimitComparison A X Y =
      AnodyneHomotopy.anodyneQ.map (mappingSpaceHammockColimitNerveMap A X Y) := by
  dsimp only [mappingSpaceHammockColimitComparison, mappingSpaceHammockColimitNerveMap]
  rw [← Category.assoc, mappingSpaceHammockGraphComparisonIso_fac,
    ← CategoryTheory.Functor.map_comp]

end SerrePositivity.EInfinity.BarrattEccles
