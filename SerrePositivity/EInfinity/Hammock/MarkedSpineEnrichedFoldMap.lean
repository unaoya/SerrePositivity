module

public import SerrePositivity.EInfinity.Hammock.MarkedSpineEnrichedFoldPoints

/-!
# 元の全因子列から任意の豊穣目標への単体写像

概要：各次数の普遍的な評価を元の全因子列の単体集合上の射に束ねる。
方針：元の全単体作用素への整合と同じ評価の合成・単位保存を使う。
規約：元の指定因子と非指定生成矢の像を回収する。
使われ方：自由積の実際の豊穣拡張。
-/

@[expose] public section
universe u uD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine
open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{u} C]

def generatorMap (W : MorphismProperty C) (g : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorTarget.Index W) :
    𝟙_ SSet.{u} ⟶ space W g.val.right g.val.left where
  app n := ↾fun _ => generatorPoint W g n
  naturality _ _ θ := by
    apply ConcreteCategory.hom_ext
    intro p
    exact (generatorPoint_simplex θ g).symm

namespace EnrichedFoldData
variable {W : MorphismProperty C} {D : Type uD} [EnrichedCategory SSet.{u} D]
  (F : EnrichedFoldData W D)

def foldMap (X Y : Paths C) : space W Y X ⟶ F.obj X ⟶[SSet.{u}] F.obj Y where
  app n := ↾fun t => F.foldPoint n t
  naturality _ _ θ := by
    apply ConcreteCategory.hom_ext
    intro t
    exact (F.foldPoint_simplex θ t).symm

lemma foldMap_unit (X : Paths C) : unitMap W X ≫ F.foldMap X X = eId SSet.{u} (F.obj X) := by
  ext n p
  exact F.foldPoint_unit

lemma foldMap_comp (X Y Z : Paths C) : composition W X Y Z ≫ F.foldMap X Z =
    (F.foldMap X Y ⊗ₘ F.foldMap Y Z) ≫ eComp SSet.{u} (F.obj X) (F.obj Y) (F.obj Z) := by
  ext n p
  exact F.foldPoint_append p.1 p.2

lemma foldMap_marked (X Y : Paths C) : nilMap W Y X ≫ F.foldMap X Y = F.marked X Y := by
  ext n p
  exact F.foldPoint_nil p

lemma foldMap_generator (g : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorTarget.Index W) :
    generatorMap W g ≫ F.foldMap g.val.left g.val.right = F.generator g := by
  ext n p
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.EnrichedDegreeCategory.category (D := D) n
  exact (F.degreeData n).fold_generatorPoint g

def enrichedFunctor :
    letI := enrichedCategory W
    EnrichedFunctor SSet.{u} (Paths C) D := by
  letI := enrichedCategory W
  exact
    { obj := F.obj
      map := F.foldMap
      map_id := F.foldMap_unit
      map_comp := F.foldMap_comp }

end EnrichedFoldData
end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine
