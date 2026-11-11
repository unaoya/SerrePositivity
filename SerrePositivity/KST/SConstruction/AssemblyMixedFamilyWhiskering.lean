module
public import SerrePositivity.KST.SConstruction.KanAssemblyMixedFamily
public import SerrePositivity.KST.SConstruction.KanAssemblyMixedWhiskering
public import SerrePositivity.KST.SConstruction.InverseMixedFamilyTransport
public import SerrePositivity.KST.SConstruction.OneDirectionInverseMixedWhiskering

/-! # 入力の前後合成と混合評価族
概要：混合選択の前後合成は、写像空間の前後合成と全次数で可換する。
方針：延長射影と持ち上げ評価の移送公式を適用する。
規約：頂点での一致ではなく単体集合の射の等号を証明する。
使われ方：指定した因子の合成三角形を構造射の写像空間へ送る。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits SSet
open Spectra Spectra.PointedMapping

/-- 延長の混合族は入力の後合成と全次数で可換する。 -/
lemma kanAssemblyMixedFamily_post (r : ℕ) {X Y Z : StableModel.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    kanAssemblyMixedPost r f g ≫ kanAssemblyMixedFamily r (f ≫ g) =
      kanAssemblyMixedFamily r f ≫
        (PointedObject.basedHomMap ((oneDirectionKanRealizationFunctor r).obj X)
          ((loopBoundaryKanFunctor (r + 1)).map g)).right := by
  have h := pointedExtensionTransport_projection
    (PointedKanReplacement.unit.app (oneDirectionReducedRealization r X))
    ((oneDirectionReducedRealizationFunctor r).map f ≫ (kanTargetAssemblyAdjointNat r).app Y)
    (PointedKanReplacement.unit.app (oneDirectionReducedRealization r X))
    ((oneDirectionReducedRealizationFunctor r).map (f ≫ g) ≫
      (kanTargetAssemblyAdjointNat r).app Z)
    (𝟙 _) (𝟙 _) ((loopBoundaryKanFunctor (r + 1)).map g) (by simp) (by
      rw [Category.id_comp, Category.assoc, ← (kanTargetAssemblyAdjointNat r).naturality g,
        CategoryTheory.Functor.map_comp, Category.assoc])
  exact h.trans (congrArg (kanAssemblyMixedFamily r f ≫ ·)
    (pointedMappingTransport_source_id _))

/-- 延長の混合族は入力の前合成と全次数で可換する。 -/
lemma kanAssemblyMixedFamily_pre (r : ℕ) {X Y Z : StableModel.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    kanAssemblyMixedPre r f g ≫ kanAssemblyMixedFamily r (f ≫ g) =
      kanAssemblyMixedFamily r g ≫
        (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed ((oneDirectionKanRealizationFunctor r).map f)
          ((loopBoundaryKanFunctor (r + 1)).obj Z)).right := by
  have h := pointedExtensionTransport_projection
    (PointedKanReplacement.unit.app (oneDirectionReducedRealization r Y))
    ((oneDirectionReducedRealizationFunctor r).map g ≫ (kanTargetAssemblyAdjointNat r).app Z)
    (PointedKanReplacement.unit.app (oneDirectionReducedRealization r X))
    ((oneDirectionReducedRealizationFunctor r).map (f ≫ g) ≫
      (kanTargetAssemblyAdjointNat r).app Z)
    ((oneDirectionReducedRealizationFunctor r).map f)
    ((oneDirectionKanRealizationFunctor r).map f) (𝟙 _)
    (PointedKanReplacement.unit.naturality ((oneDirectionReducedRealizationFunctor r).map f))
    (by rw [Category.comp_id, CategoryTheory.Functor.map_comp, Category.assoc])
  exact h.trans (congrArg (kanAssemblyMixedFamily r g ≫ ·)
    (pointedMappingTransport_target_id _))

/-- 逆射の混合族は入力の後合成と全次数で可換する。 -/
lemma oneDirectionInverseMixedFamily_post (r : ℕ) {X Y Z : StableModel.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    oneDirectionInverseMixedPost r f g ≫ oneDirectionInverseMixedFamily r (f ≫ g) =
      oneDirectionInverseMixedFamily r f ≫
        (PointedObject.basedHomMap ((boundaryKanRealizationFunctor r).obj X)
          ((oneDirectionKanRealizationFunctor r).map g)).right := by
  have h := pointedLiftTransport_evaluation
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathProjection ((oneDirectionKanComparisonNat r).app Y))
    ((boundaryKanRealizationFunctor r).map f)
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathProjection ((oneDirectionKanComparisonNat r).app Z))
    ((boundaryKanRealizationFunctor r).map (f ≫ g))
    (𝟙 _) (oneDirectionMappingPathMap r g) ((boundaryKanRealizationFunctor r).map g)
    (oneDirectionMappingPathMap_projection r g)
    (by simp only [Category.id_comp, CategoryTheory.Functor.map_comp])
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathRetraction ((oneDirectionKanComparisonNat r).app Y))
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathRetraction ((oneDirectionKanComparisonNat r).app Z))
    ((oneDirectionKanRealizationFunctor r).map g) (oneDirectionMappingPathMap_retraction r g)
  have hu := congrArg (oneDirectionInverseMixedFamily r f ≫ ·)
    (pointedMappingTransport_source_id ((oneDirectionKanRealizationFunctor r).map g))
  exact h.trans ((Category.assoc _ _ _).symm.trans hu)

/-- 逆射の混合族は入力の前合成と全次数で可換する。 -/
lemma oneDirectionInverseMixedFamily_pre (r : ℕ) {X Y Z : StableModel.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    oneDirectionInverseMixedPre r f g ≫ oneDirectionInverseMixedFamily r (f ≫ g) =
      oneDirectionInverseMixedFamily r g ≫
        (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed ((boundaryKanRealizationFunctor r).map f)
          ((oneDirectionKanRealizationFunctor r).obj Z)).right := by
  have h := pointedLiftTransport_evaluation
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathProjection ((oneDirectionKanComparisonNat r).app Z))
    ((boundaryKanRealizationFunctor r).map g)
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathProjection ((oneDirectionKanComparisonNat r).app Z))
    ((boundaryKanRealizationFunctor r).map (f ≫ g))
    ((boundaryKanRealizationFunctor r).map f) (𝟙 _) (𝟙 _) (by simp)
    (by simp only [Category.comp_id, CategoryTheory.Functor.map_comp])
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathRetraction ((oneDirectionKanComparisonNat r).app Z))
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathRetraction ((oneDirectionKanComparisonNat r).app Z)) (𝟙 _) (by simp)
  have hu := congrArg (oneDirectionInverseMixedFamily r g ≫ ·)
    (pointedMappingTransport_target_id ((boundaryKanRealizationFunctor r).map f))
  exact h.trans ((Category.assoc _ _ _).symm.trans hu)

end SerrePositivity.KST.SConstruction
