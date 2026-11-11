module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ConeRestrictionTransport

/-!
概要：形状の pushout 上の coherent な錐の全空間を、元の二部分から一意に貼る。
方針：任意パラメータと形状の join の pushout で uncurry した錐を貼り合わせる。
規約：元の図式・頂点の全単体を保持。使われ方：固定頂点の錐空間の引き戻し表示。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.F2
variable {A B C D T X : SSet.{u}} {f : A ⟶ B} {g : A ⟶ C}
  {i : B ⟶ D} {j : C ⟶ D} (hp : IsPushout f g i j) (p : D ⟶ X)

/-- 全体から二部分を経た共通部分への錐の制限は全単体で一致する。 -/
lemma sliceShapePushout_comm :
    sliceOverRestrict p i ≫ sliceOverRestrict (i ≫ p) f =
      sliceOverRestrict p j ≫
        normalizedConeRestriction (j ≫ p) g (conePushoutBoundary_eq hp p) := by
  apply sliceOverUncurry_injective (f ≫ (i ≫ p))
  have hr {L : SSet.{u}} (k : L ⟶ D) :
      sliceOverUncurry (sliceOverRestrict p k) =
        joinMap (𝟙 (sliceOver p)) k ≫ sliceOverUncurry (𝟙 (sliceOver p)) := by
    simpa only [Category.id_comp] using sliceOverUncurry_restrict (𝟙 (sliceOver p)) k
  rw [sliceOverUncurry_restrict, normalizedConeRestriction_uncurry, hr i, hr j,
    ← Category.assoc, ← joinMap_comp, ← Category.assoc, ← joinMap_comp]
  simp only [Category.id_comp, hp.w]

/-- 境界で一致する元の二部分の錐の族を、全図式の錐の族へ一意に貼り合わせる。 -/
lemma sliceShapePushout_lift (b : T ⟶ sliceOver (i ≫ p)) (c : T ⟶ sliceOver (j ≫ p))
    (h : b ≫ sliceOverRestrict (i ≫ p) f =
      c ≫ normalizedConeRestriction (j ≫ p) g (conePushoutBoundary_eq hp p)) :
    ∃! a : T ⟶ sliceOver p,
      a ≫ sliceOverRestrict p i = b ∧ a ≫ sliceOverRestrict p j = c := by
  have hh := congrArg sliceOverUncurry h
  rw [sliceOverUncurry_restrict, normalizedConeRestriction_uncurry] at hh
  let hs := join_right_isPushout hp T
  let H := hs.desc (sliceOverUncurry b) (sliceOverUncurry c) hh
  have hH : joinInr T D ≫ H = p := by
    apply hp.hom_ext
    · rw [← Category.assoc, ← joinInr_joinMap, Category.assoc, hs.inl_desc]
      exact sliceOverUncurry_fixed b
    · rw [← Category.assoc, ← joinInr_joinMap, Category.assoc, hs.inr_desc]
      exact sliceOverUncurry_fixed c
  let a := sliceOverCurry H hH
  have ha : sliceOverUncurry a = H := sliceOverUncurry_curry _ _
  refine ⟨a, ⟨?_, ?_⟩, ?_⟩
  · apply sliceOverUncurry_injective (i ≫ p)
    rw [sliceOverUncurry_restrict, ha]
    exact hs.inl_desc _ _ _
  · apply sliceOverUncurry_injective (j ≫ p)
    rw [sliceOverUncurry_restrict, ha]
    exact hs.inr_desc _ _ _
  · intro m hm
    apply sliceOverUncurry_injective p
    rw [ha]
    apply hs.hom_ext
    · rw [← sliceOverUncurry_restrict, hm.1]
      exact (hs.inl_desc _ _ _).symm
    · rw [← sliceOverUncurry_restrict, hm.2]
      exact (hs.inr_desc _ _ _).symm

end SerrePositivity.InfinityCategories.F2
