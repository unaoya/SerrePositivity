module
public import SerrePositivity.KST.SConstruction.MappingPathTransport
public import SerrePositivity.KST.SConstruction.OneDirectionInverseChoices

/-! # 一方向比較の mapping path の関手
概要：元の比較の自然性から mapping path の厳密な関手を構成する。
方針：可換正方形の移送とその関手法則を使う。
規約：元の二つの Kan 模型と射影を保持する。
使われ方：逆射の混合切断空間の自然性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open Spectra

/-- 入力の射を一方向比較の mapping path の射へ移す。 -/
def oneDirectionMappingPathMap (r : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y) :
    _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPath ((oneDirectionKanComparisonNat r).app X) ⟶
      _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPath ((oneDirectionKanComparisonNat r).app Y) :=
  mappingPathTransport _ _ ((oneDirectionKanRealizationFunctor r).map f)
    ((boundaryKanRealizationFunctor r).map f) ((oneDirectionKanComparisonNat r).naturality f)

/-- 一方向比較の mapping path の移送は恒等射を保つ。 -/
lemma oneDirectionMappingPathMap_id (r : ℕ) (X : StableModel.{u}) :
    oneDirectionMappingPathMap r (𝟙 X) = 𝟙 _ := by
  dsimp only [oneDirectionMappingPathMap]
  simp only [CategoryTheory.Functor.map_id]
  exact mappingPathTransport_id _

/-- 一方向比較の mapping path の移送は合成を保つ。 -/
lemma oneDirectionMappingPathMap_comp (r : ℕ) {X Y Z : StableModel.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    oneDirectionMappingPathMap r (f ≫ g) = oneDirectionMappingPathMap r f ≫
      oneDirectionMappingPathMap r g := by
  dsimp only [oneDirectionMappingPathMap]
  simp only [CategoryTheory.Functor.map_comp]
  exact (mappingPathTransport_comp _ _ _ _ _ _ _ _ _ _).symm

/-- 一方向比較の mapping path を厳密な関手へ束ねる。 -/
def oneDirectionMappingPathFunctor (r : ℕ) : StableModel.{u} ⥤ PointedSimplicialSet.{u} where
  obj X := _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPath ((oneDirectionKanComparisonNat r).app X)
  map f := oneDirectionMappingPathMap r f
  map_id X := oneDirectionMappingPathMap_id r X
  map_comp f g := oneDirectionMappingPathMap_comp r f g

/-- mapping path から境界への射影の厳密な自然性。 -/
lemma oneDirectionMappingPathMap_projection (r : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y) :
    oneDirectionMappingPathMap r f ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathProjection ((oneDirectionKanComparisonNat r).app Y) =
      _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathProjection ((oneDirectionKanComparisonNat r).app X) ≫
        (boundaryKanRealizationFunctor r).map f := mappingPathTransport_projection ..

/-- mapping path から一方向模型への射影の厳密な自然性。 -/
lemma oneDirectionMappingPathMap_retraction (r : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y) :
    oneDirectionMappingPathMap r f ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathRetraction ((oneDirectionKanComparisonNat r).app Y) =
      _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathRetraction ((oneDirectionKanComparisonNat r).app X) ≫
        (oneDirectionKanRealizationFunctor r).map f := mappingPathTransport_retraction ..

end SerrePositivity.KST.SConstruction
