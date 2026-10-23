module

public import SerrePositivity.InfinityCategories.F1.Joins.SlicePrismSquare
public import SerrePositivity.InfinityCategories.F1.Coherent.PrismEvaluation

/-!
概要：元の右 Hom の豊穣合成を、三つの辺と定値辺を持つ一つの四角形に束ねる。
方針：既存の終点固定の合成 prism を同じ右 join 区間で展開し、四辺を厳密に同定する。
規約：二つの元の Hom 全体をパラメーターとし、反転しない。
使われ方：右 Hom の pointed 評価と元の内部 Hom の評価の両立。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 二つの元の Hom の合成を、三辺と定値な最終辺を持つ同じ四角形にする。 -/
def coherentCompositionSquare {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (X Y Z : C) :
    Δ[1] ⊗ (Δ[1] ⊗ ((SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom X Y) ⊗
      (SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom Y Z))) ⟶ SimplicialNerve C :=
  slicePrismSquare (coherentNerveVertex Z) (coherentCompositionPrism X Y Z)

/-- 外側の零端は、最初の射の元の右 Hom の区間族。 -/
lemma coherentCompositionSquare_zero {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (X Y Z : C) :
    prismEndpoint 0 _ ≫ coherentCompositionSquare X Y Z =
      (Δ[1] ◁ fst _ _) ≫ intervalMappingUncurry
        (coherentHomComparison X Y ≫ pinchedHomToIntervalMappingSpace _ _) := by
  rw [coherentCompositionSquare, slicePrismSquare_zero, coherentCompositionPrism_projection]

/-- 外側の一端は、固定した最終対象 Z に厳密に定値。 -/
lemma coherentCompositionSquare_one {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (X Y Z : C) :
    prismEndpoint 1 _ ≫ coherentCompositionSquare X Y Z =
      SSet.const (coherentNerveVertex Z) :=
  slicePrismSquare_one (coherentNerveVertex Z) (coherentCompositionPrism X Y Z)

/-- 内側の零端は、元の豊穣合成の右 Hom の区間族そのもの。 -/
lemma coherentCompositionSquare_inner_zero
    {C : Type v} [Category.{u} C] [SimplicialCategory C] (X Y Z : C) :
    (Δ[1] ◁ prismEndpoint 0 _) ≫ coherentCompositionSquare X Y Z =
      intervalMappingUncurry
        (coherentHomComposition X Y Z ≫ coherentHomComparison X Z ≫
          pinchedHomToIntervalMappingSpace _ _) := by
  rw [coherentCompositionSquare, slicePrismSquare_inner, coherentCompositionPrism_zero]
  change rightMappingSpacePrism _ ≫
    pinchedHomUncurry (coherentHomComposition X Y Z ≫ coherentHomComparison X Z) = _
  exact (pinchedHomToIntervalMappingSpace_uncurry
    (coherentHomComposition X Y Z ≫ coherentHomComparison X Z)).symm

/-- 内側の一端は、二番目の射の元の右 Hom の区間族そのもの。 -/
lemma coherentCompositionSquare_inner_one
    {C : Type v} [Category.{u} C] [SimplicialCategory C] (X Y Z : C) :
    (Δ[1] ◁ prismEndpoint 1 _) ≫ coherentCompositionSquare X Y Z =
      intervalMappingUncurry (snd _ _ ≫ coherentHomComparison Y Z ≫
        pinchedHomToIntervalMappingSpace _ _) := by
  rw [coherentCompositionSquare, slicePrismSquare_inner, coherentCompositionPrism_one]
  change rightMappingSpacePrism _ ≫ pinchedHomUncurry (snd _ _ ≫ coherentHomComparison Y Z) = _
  exact (pinchedHomToIntervalMappingSpace_uncurry (snd _ _ ≫ coherentHomComparison Y Z)).symm

end SerrePositivity.InfinityCategories
