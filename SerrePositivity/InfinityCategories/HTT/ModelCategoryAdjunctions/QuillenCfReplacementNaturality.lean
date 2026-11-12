module

public import SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.QuillenCfReplacementFunctors
public import SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.QuillenCfMixedComposition

/-!
概要：元の通常の置換比較射を、同じ cf 対応圏の厳密な自然変換へ束ねる。
方針：元の Hom 同型の合成式と、元の通常の置換比較の自然性を使用する。
規約：coherent な cf 置換関手の射との照合は別工程。使われ方：HTT 5.2.4.6。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory MonoidalClosed SSet HomotopicalAlgebra
open SerrePositivity.HomotopyFunctionComplex

open SerrePositivity.KST.SConstruction
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions
noncomputable section

variable {C D : Type v} [Category.{u} C] [Category.{u} D]
  [SimplicialCategory C] [SimplicialCategory D] [ModelCategory C] [ModelCategory D]
  (R : EnrichedFunctor SSet.{u} D C) {L : C ⥤ D}
  (adj : L ⊣ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor R) [SerrePositivity.Quillen.IsLeftQuillen L]
  (cofC : MorphismProperty.FunctorialFactorizationData
    (cofibrations C) (trivialFibrations C))
  (fibD : MorphismProperty.FunctorialFactorizationData
    (trivialCofibrations D) (fibrations D))

/-- 元の Q(RY)→RY の混合射は、元の通常の置換関手の射に厳密に自然である。 -/
lemma quillenCfRightLiftArrow_naturality {Y Z : _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.CofibrantFibrantObjects D} (a : Y ⟶ Z) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageBottom R)).map
        ((_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfRightReplacementFunctor R adj cofC).map a) ≫
      _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfRightLiftArrow R adj cofC Z =
    _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfRightLiftArrow R adj cofC Y ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageTop R)).map a := by
  apply (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfMixedHomEquiv R (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfRightLiftObject R adj cofC Y) Z).injective
  rw [_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfMixedHomEquiv_bottom_comp, _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfMixedHomEquiv_comp_top]
  change (cofibrantSource cofC).map ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor R).map a.hom) ≫
      _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfMixedHomEquiv R (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfRightLiftObject R adj cofC Z) Z
        (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfRightLiftArrow R adj cofC Z) =
    _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfMixedHomEquiv R (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfRightLiftObject R adj cofC Y) Y
      (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfRightLiftArrow R adj cofC Y) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor R).map a.hom
  rw [_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfRightLiftArrow_original, _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfRightLiftArrow_original]
  exact (cofibrantSourceComparison cofC).naturality _

/-- 元の LX→R_D(LX) の随伴像は、元の通常の置換関手の射に厳密に自然である。 -/
lemma quillenCfLeftLiftArrow_naturality {X W : _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.CofibrantFibrantObjects C} (a : X ⟶ W) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageBottom R)).map a ≫
      _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfLeftLiftArrow R adj fibD W =
    _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfLeftLiftArrow R adj fibD X ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageTop R)).map
        ((_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfLeftReplacementFunctor R adj fibD).map a) := by
  apply (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfMixedHomEquiv R X (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfLeftLiftObject R adj fibD W)).injective
  rw [_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfMixedHomEquiv_bottom_comp, _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfMixedHomEquiv_comp_top,
    _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfLeftLiftArrow_original, _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfLeftLiftArrow_original]
  calc
    _ = adj.homEquiv X.obj ((fibrantTarget fibD).obj (L.obj W.obj))
        (L.map a.hom ≫ (fibrantTargetComparison fibD).app (L.obj W.obj)) :=
      (adj.homEquiv_naturality_left a.hom
        ((fibrantTargetComparison fibD).app (L.obj W.obj))).symm
    _ = adj.homEquiv X.obj ((fibrantTarget fibD).obj (L.obj W.obj))
        ((fibrantTargetComparison fibD).app (L.obj X.obj) ≫
          (fibrantTarget fibD).map (L.map a.hom)) :=
      congrArg (adj.homEquiv X.obj ((fibrantTarget fibD).obj (L.obj W.obj)))
        ((fibrantTargetComparison fibD).naturality (L.map a.hom))
    _ = _ := adj.homEquiv_naturality_right
      ((fibrantTargetComparison fibD).app (L.obj X.obj))
      ((fibrantTarget fibD).map (L.map a.hom))

/-- 元の右の置換比較射を、元の通常の置換関手と両包含の自然変換へ束ねる。 -/
def quillenCfRightReplacementComparison :
    _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfRightReplacementFunctor R adj cofC ⋙
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageBottom R) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageTop R) where
  app Y := _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfRightLiftArrow R adj cofC Y
  naturality {_ _} a := quillenCfRightLiftArrow_naturality R adj cofC a

/-- 元の左の置換比較射を、元の通常の置換関手と両包含の自然変換へ束ねる。 -/
def quillenCfLeftReplacementComparison :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageBottom R) ⟶
      _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfLeftReplacementFunctor R adj fibD ⋙
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageTop R) where
  app X := _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfLeftLiftArrow R adj fibD X
  naturality {_ _} a := quillenCfLeftLiftArrow_naturality R adj fibD a

end
end SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions
