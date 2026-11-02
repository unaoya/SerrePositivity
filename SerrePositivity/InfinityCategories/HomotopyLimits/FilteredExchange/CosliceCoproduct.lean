module

public import SerrePositivity.InfinityCategories.Core.Coslice
public import SerrePositivity.InfinityCategories.Core.Join
public import SerrePositivity.InfinityCategories.Core.JoinCoproductPushout
public import SerrePositivity.InfinityCategories.Core.JoinLifting
public import SerrePositivity.InfinityCategories.Core.RightFibration
public import SerrePositivity.InfinityCategories.Core.Slice
public import SerrePositivity.InfinityCategories.Core.SliceMap
public import SerrePositivity.InfinityCategories.HomotopyLimits.CoconeRestrictionTransport
public import SerrePositivity.InfinityCategories.HomotopyLimits.CosliceShapePushout

/-!
概要：二つの図式の coproduct の coslice は、頂点射影どうしの厳密な引き戻し。
方針：共通の頂点族に沿って join の射を貼り合わせる。
規約：図式と全パラメータの頂点を厳密に保つ。
使われ方：filtered な coslice の射影の Quillen A 条件。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits

/-- 概要：図式の和から第一の図式への正規化した coslice の制限。
方針：第一包含との合成の等式で移送する。
規約：元の p を終域に使う。使われ方：coslice の引き戻し比較の第一射。 -/
def cosliceCoproductFst {K L C : SSet.{u}} (p : K ⟶ C) (q : L ⟶ C) :
    sliceUnder (coprod.desc p q) ⟶ sliceUnder p :=
  normalizedCoconeRestriction _ coprod.inl (coprod.inl_desc p q)

/-- 概要：図式の和から第二の図式への正規化した coslice の制限。
方針：第二包含との合成の等式で移送する。
規約：元の q を終域に使う。使われ方：coslice の引き戻し比較の第二射。 -/
def cosliceCoproductSnd {K L C : SSet.{u}} (p : K ⟶ C) (q : L ⟶ C) :
    sliceUnder (coprod.desc p q) ⟶ sliceUnder q :=
  normalizedCoconeRestriction _ coprod.inr (coprod.inr_desc p q)

/-- 概要：図式の coproduct の coslice は、二つの頂点射影の引き戻し。
方針：共通の頂点を持つ二つの余錐族を join の押し出しで貼る。
規約：quasicategory 性や有限性は不要。使われ方：comma の正確な表示。 -/
lemma cosliceCoproduct_isPullback {K L C : SSet.{u}} (p : K ⟶ C) (q : L ⟶ C) :
    IsPullback (cosliceCoproductFst p q) (cosliceCoproductSnd p q)
      (sliceUnderProjection p) (sliceUnderProjection q) := by
  have hc : cosliceCoproductFst p q ≫ sliceUnderProjection p =
      cosliceCoproductSnd p q ≫ sliceUnderProjection q := by
    simp only [cosliceCoproductFst, cosliceCoproductSnd, normalizedCoconeRestriction_projection]
  apply IsPullback.of_isLimit (c := PullbackCone.mk _ _ hc)
  apply PullbackCone.isLimitAux'
  intro s
  let hs := join_coproduct_isPushout K L s.pt
  have he : joinInr K s.pt ≫ sliceUnderUncurry s.fst =
      joinInr L s.pt ≫ sliceUnderUncurry s.snd := by
    rw [sliceUnderUncurry_projection, sliceUnderUncurry_projection]
    exact s.condition
  let H := hs.desc (sliceUnderUncurry s.fst) (sliceUnderUncurry s.snd) he
  have hH : joinInl (K ⨿ L) s.pt ≫ H = coprod.desc p q := by
    apply coprod.hom_ext
    · rw [← Category.assoc, ← joinInl_joinMap, Category.assoc, hs.inl_desc,
        sliceUnderUncurry_fixed]
      exact (coprod.inl_desc p q).symm
    · rw [← Category.assoc, ← joinInl_joinMap, Category.assoc, hs.inr_desc,
        sliceUnderUncurry_fixed]
      exact (coprod.inr_desc p q).symm
  let a := sliceUnderCurry H hH
  have ha : sliceUnderUncurry a = H := sliceUnderUncurry_curry _ _
  have h₁ : a ≫ cosliceCoproductFst p q = s.fst := by
    apply sliceUnderUncurry_injective p
    rw [cosliceCoproductFst, normalizedCoconeRestriction_uncurry, ha]
    exact hs.inl_desc _ _ _
  have h₂ : a ≫ cosliceCoproductSnd p q = s.snd := by
    apply sliceUnderUncurry_injective q
    rw [cosliceCoproductSnd, normalizedCoconeRestriction_uncurry, ha]
    exact hs.inr_desc _ _ _
  refine ⟨a, h₁, h₂, ?_⟩
  intro m hm₁ hm₂
  apply sliceUnderUncurry_injective (coprod.desc p q)
  rw [ha]
  apply hs.hom_ext
  · have h : sliceUnderUncurry (m ≫ normalizedCoconeRestriction
        (coprod.desc p q) coprod.inl (coprod.inl_desc p q)) = sliceUnderUncurry s.fst :=
      congrArg sliceUnderUncurry hm₁
    rw [normalizedCoconeRestriction_uncurry] at h
    exact h.trans (hs.inl_desc _ _ _).symm
  · have h : sliceUnderUncurry (m ≫ normalizedCoconeRestriction
        (coprod.desc p q) coprod.inr (coprod.inr_desc p q)) = sliceUnderUncurry s.snd :=
      congrArg sliceUnderUncurry hm₂
    rw [normalizedCoconeRestriction_uncurry] at h
    exact h.trans (hs.inr_desc _ _ _).symm

end SerrePositivity.InfinityCategories.F2
