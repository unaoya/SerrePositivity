module
public import SerrePositivity.KST.SConstruction.OneDirectionInverseMixedNaturality
public import SerrePositivity.KST.SConstruction.PointedMappingTransportUnits

/-! # 比較逆射の混合族の厳密な両端制限
概要：逆射の混合パラメーター族の両端を元の逆射の族の前後合成と同定する。
方針：持ち上げの移送・写像空間の後合成・両射影の自然性を使う。
規約：全パラメーターの射として等号を証明する。
使われ方：逆射と延長の自然性の二つの族の厳密な貼り合わせ。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits SSet
open Spectra Spectra.PointedMapping

/-- 持ち上げの族を別の射で評価することは可換正方形の移送と可換。 -/
lemma pointedLiftTransport_evaluation {A E B R A' E' B' R' : PointedSimplicialSet.{u}}
    (p : E ⟶ B) (b : A ⟶ B) (p' : E' ⟶ B') (b' : A' ⟶ B')
    (a : A' ⟶ A) (e : E ⟶ E') (c : B ⟶ B')
    (hp : e ≫ p' = p ≫ c) (hb : a ≫ b ≫ c = b')
    (s : E ⟶ R) (s' : E' ⟶ R') (d : R ⟶ R') (hs : e ≫ s' = s ≫ d) :
    pointedLiftTransport p b p' b' a e c hp hb ≫
      (pullback.fst (PointedObject.basedHomMap A' p').right
        (SSet.yonedaEquiv.symm (familyVertex b')) ≫ (PointedObject.basedHomMap A' s').right) =
    pullback.fst (PointedObject.basedHomMap A p).right
      (SSet.yonedaEquiv.symm (familyVertex b)) ≫ (PointedObject.basedHomMap A s).right ≫
        pointedMappingTransport a d := by
  rw [← Category.assoc, pointedLiftTransport_projection, Category.assoc,
    pointedMappingTransport_post a e d s s' hs]

/-- 源の逆射選択の全次数で、混合族は元の逆射の族の後合成に一致する。 -/
lemma oneDirectionInverseMixedFamily_source (r : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y) :
    oneDirectionInverseMixedFromSource r f ≫ oneDirectionInverseMixedFamily r f =
      pointedMappingPathInverseFamily ((oneDirectionKanComparisonNat r).app X) ≫
        (PointedObject.basedHomMap ((boundaryKanRealizationFunctor r).obj X)
          ((oneDirectionKanRealizationFunctor r).map f)).right := by
  have h := pointedLiftTransport_evaluation
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathProjection ((oneDirectionKanComparisonNat r).app X)) (𝟙 _)
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathProjection ((oneDirectionKanComparisonNat r).app Y))
    ((boundaryKanRealizationFunctor r).map f)
    (𝟙 _) (oneDirectionMappingPathMap r f) ((boundaryKanRealizationFunctor r).map f)
    (oneDirectionMappingPathMap_projection r f) (by simp)
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathRetraction ((oneDirectionKanComparisonNat r).app X))
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathRetraction ((oneDirectionKanComparisonNat r).app Y))
    ((oneDirectionKanRealizationFunctor r).map f) (oneDirectionMappingPathMap_retraction r f)
  have hu := congrArg
    (pointedMappingPathInverseFamily ((oneDirectionKanComparisonNat r).app X) ≫ ·)
    (pointedMappingTransport_source_id ((oneDirectionKanRealizationFunctor r).map f))
  exact h.trans ((Category.assoc _ _ _).symm.trans hu)

/-- 標的の逆射選択の全次数で、混合族は元の逆射の族の前合成に一致する。 -/
lemma oneDirectionInverseMixedFamily_target (r : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y) :
    oneDirectionInverseMixedFromTarget r f ≫ oneDirectionInverseMixedFamily r f =
      pointedMappingPathInverseFamily ((oneDirectionKanComparisonNat r).app Y) ≫
        (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed ((boundaryKanRealizationFunctor r).map f)
          ((oneDirectionKanRealizationFunctor r).obj Y)).right := by
  have h := pointedLiftTransport_evaluation
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathProjection ((oneDirectionKanComparisonNat r).app Y)) (𝟙 _)
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathProjection ((oneDirectionKanComparisonNat r).app Y))
    ((boundaryKanRealizationFunctor r).map f)
    ((boundaryKanRealizationFunctor r).map f) (𝟙 _) (𝟙 _) (by simp) (by simp)
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathRetraction ((oneDirectionKanComparisonNat r).app Y))
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathRetraction ((oneDirectionKanComparisonNat r).app Y)) (𝟙 _) (by simp)
  have hu := congrArg
    (pointedMappingPathInverseFamily ((oneDirectionKanComparisonNat r).app Y) ≫ ·)
    (pointedMappingTransport_target_id ((boundaryKanRealizationFunctor r).map f))
  exact h.trans ((Category.assoc _ _ _).symm.trans hu)

end SerrePositivity.KST.SConstruction
