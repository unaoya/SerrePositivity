module

public import SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.QuillenCfRightLift
public import SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.QuillenCfLeftLift

/-!
概要：元の関手的因子分解をそのまま使う、通常の左右の cf 置換関手。
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

/-- 元の cofibrant 置換 Q と右関手 R の通常の合成を、元の cf 対象へ制限する。 -/
def quillenCfRightReplacementFunctor : _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.CofibrantFibrantObjects D ⥤ _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.CofibrantFibrantObjects C where
  obj := _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfRightLiftObject R adj cofC
  map f := ⟨(cofibrantSource cofC).map ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor R).map f.hom)⟩
  map_id X := by
    apply InducedCategory.hom_ext
    change (cofibrantSource cofC).map
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor R).map (𝟙 X.obj)) = 𝟙 _
    simp only [CategoryTheory.Functor.map_id]
  map_comp f g := by
    apply InducedCategory.hom_ext
    change (cofibrantSource cofC).map
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor R).map (f.hom ≫ g.hom)) =
      (cofibrantSource cofC).map ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor R).map f.hom) ≫
        (cofibrantSource cofC).map ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor R).map g.hom)
    simp only [CategoryTheory.Functor.map_comp]

/-- 元の左関手 L と fibrant 置換の通常の合成を、元の cf 対象へ制限する。 -/
def quillenCfLeftReplacementFunctor : _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.CofibrantFibrantObjects C ⥤ _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.CofibrantFibrantObjects D where
  obj := _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfLeftLiftObject R adj fibD
  map f := ⟨(fibrantTarget fibD).map (L.map f.hom)⟩
  map_id X := by
    apply InducedCategory.hom_ext
    change (fibrantTarget fibD).map (L.map (𝟙 X.obj)) = 𝟙 _
    simp only [CategoryTheory.Functor.map_id]
  map_comp f g := by
    apply InducedCategory.hom_ext
    change (fibrantTarget fibD).map (L.map (f.hom ≫ g.hom)) =
      (fibrantTarget fibD).map (L.map f.hom) ≫ (fibrantTarget fibD).map (L.map g.hom)
    simp only [CategoryTheory.Functor.map_comp]

end
end SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions
