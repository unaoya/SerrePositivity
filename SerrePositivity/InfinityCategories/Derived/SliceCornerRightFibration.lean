module
public import SerrePositivity.InfinityCategories.Derived.RelativeSliceRightFibration
public import SerrePositivity.InfinityCategories.Derived.InitialIndexSlice
public import SerrePositivity.InfinityCategories.F1B.KanSliceProjectionLaws
/-!
概要：inner fibration の実 slice を、標的の slice と元の始域の corner へ写すと右ファイブレーション。
方針：空部分図式の相対 slice の右ファイブレーションを、空 slice の厳密同型で正規化する。
規約：モデル圏構造は使わない。使われ方：商側三角形から商屋根への右ファイブレーション。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits SSet
variable {K E B : SSet.{u}} (p : K ⟶ E) (r : E ⟶ B)
/-- 標的の実 slice と元の同じ始域を保持する corner。 -/
def sliceOverCorner : SSet.{u} := pullback (sliceOverProjection (p ≫ r)) r
/-- 実 slice の各錐を、標的の全錐と元の始域の組へ写す。 -/
def sliceOverCornerMap : sliceOver p ⟶ sliceOverCorner p r :=
  pullback.lift (sliceOverPostcomp p r) (sliceOverProjection p)
    (F1B.kanSliceOverPostcomp_projection p r)
/-- 空部分図式の相対 slice を、元の始域を記憶する corner へ厳密に正規化する。 -/
def relativeSliceEmptyCornerMap :
    relativeSliceOver p (⊥ : K.Subcomplex).ι r ⟶ sliceOverCorner p r :=
  pullback.map (sliceOverRestrict (p ≫ r) (⊥ : K.Subcomplex).ι)
    (sliceOverPostcomp ((⊥ : K.Subcomplex).ι ≫ p) r)
    (sliceOverProjection (p ≫ r)) r (𝟙 _)
    (sliceOverProjection ((⊥ : K.Subcomplex).ι ≫ p))
    (sliceOverProjection (((⊥ : K.Subcomplex).ι ≫ p) ≫ r))
    (by simpa only [Category.id_comp] using!
      F1B.kanSliceOverRestrict_projection (p ≫ r) (⊥ : K.Subcomplex).ι)
    (F1B.kanSliceOverPostcomp_projection ((⊥ : K.Subcomplex).ι ≫ p) r)
/-- 空部分図式の正規化は、全次数で厳密な同型。 -/
instance relativeSliceEmptyCornerMap_isIso : IsIso (relativeSliceEmptyCornerMap p r) := by
  have := initialIndexSliceProjection_isIso Subcomplex.isInitialBot
    ((⊥ : K.Subcomplex).ι ≫ p)
  have := initialIndexSliceProjection_isIso Subcomplex.isInitialBot
    (((⊥ : K.Subcomplex).ι ≫ p) ≫ r)
  dsimp only [relativeSliceEmptyCornerMap]
  infer_instance
/-- 空相対 slice の正規化は、元の同じ全錐の corner 写像を回収する。 -/
lemma relativeSliceOverMap_empty_corner :
    relativeSliceOverMap p (⊥ : K.Subcomplex).ι r ≫ relativeSliceEmptyCornerMap p r =
      sliceOverCornerMap p r := by
  apply pullback.hom_ext
  · dsimp only [relativeSliceEmptyCornerMap, sliceOverCornerMap, relativeSliceOverMap,
      pullback.map]
    rw [Category.assoc, pullback.lift_fst, ← Category.assoc,
      pullback.lift_fst, Category.comp_id, pullback.lift_fst]
  · dsimp only [relativeSliceEmptyCornerMap, sliceOverCornerMap, relativeSliceOverMap,
      pullback.map]
    rw [Category.assoc, pullback.lift_snd, ← Category.assoc,
      pullback.lift_snd, pullback.lift_snd]
    exact F1B.kanSliceOverRestrict_projection p (⊥ : K.Subcomplex).ι
/-- inner fibration の実 slice の corner 比較は右ファイブレーション。 -/
instance sliceOverCornerMap_rightFibration [InnerFibration r] :
    RightFibration (sliceOverCornerMap p r) := by
  have : RightFibration (relativeSliceEmptyCornerMap p r) :=
    ⟨rightFibrations.of_isIso _⟩
  have h : RightFibration (relativeSliceOverMap p (⊥ : K.Subcomplex).ι r ≫
      relativeSliceEmptyCornerMap p r) :=
    ⟨rightFibrations.comp_mem _ _ RightFibration.mem RightFibration.mem⟩
  rw [relativeSliceOverMap_empty_corner] at h
  exact h
end SerrePositivity.InfinityCategories
