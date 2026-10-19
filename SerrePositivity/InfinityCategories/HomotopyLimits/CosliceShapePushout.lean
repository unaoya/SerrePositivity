module

public import SerrePositivity.InfinityCategories.HomotopyLimits.CoconeRestrictionTransport
public import SerrePositivity.InfinityCategories.HomotopyLimits.CoconeBoundaryRectification

/-!
概要：形状の押し出し上の余錐全体を、二つの部分余錐の coslice の厳密な引き戻しで表す。
方針：任意のパラメータと形状の join の押し出しに沿って uncurry した族を貼り合わせる。
規約：頂点の全単体も含めて比較する。充填性・余極限性・単射性は不要。
使われ方：部分余極限の Hom 表示を、元の coherent 図式の余極限性へ接続する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section

/-- 正規化した余錐の制限の uncurry は、形状側の joinMap による前合成。 -/
lemma normalizedCoconeRestriction_uncurry {A C T X : SSet.{u}} {p : A ⟶ X}
    (F : C ⟶ X) (i : A ⟶ C) (hi : i ≫ F = p) (a : T ⟶ sliceUnder F) :
    sliceUnderUncurry (a ≫ normalizedCoconeRestriction F i hi) =
      joinMap i (𝟙 T) ≫ sliceUnderUncurry a := by
  cases hi
  simp only [normalizedCoconeRestriction, eqToHom_refl, Category.comp_id]
  exact sliceUnderUncurry_restrict a i

variable {A B C D T X : SSet.{u}}
  {f : A ⟶ B} {g : A ⟶ C} {i : B ⟶ D} {j : C ⟶ D}
  (hp : IsPushout f g i j) (p : D ⟶ X)

/-- 全体から二つの部分を経由した共通部分への余錐の制限は、全単体で一致する。 -/
lemma cosliceShapePushout_comm :
    sliceUnderRestrict p i ≫ sliceUnderRestrict (i ≫ p) f =
      sliceUnderRestrict p j ≫
        normalizedCoconeRestriction (j ≫ p) g (coconePushoutBoundary_eq hp p) := by
  apply sliceUnderUncurry_injective (f ≫ (i ≫ p))
  have hr {L : SSet.{u}} (k : L ⟶ D) :
      sliceUnderUncurry (sliceUnderRestrict p k) =
        joinMap k (𝟙 (sliceUnder p)) ≫ sliceUnderUncurry (𝟙 (sliceUnder p)) := by
    simpa only [Category.id_comp] using sliceUnderUncurry_restrict (𝟙 (sliceUnder p)) k
  rw [sliceUnderUncurry_restrict, normalizedCoconeRestriction_uncurry, hr i, hr j,
    ← Category.assoc, ← joinMap_comp, ← Category.assoc, ← joinMap_comp]
  simp only [Category.id_comp, hp.w]

/-- 境界で一致する余錐の任意のパラメータ族は、元の図式上へ一意に貼り合わせられる。 -/
lemma cosliceShapePushout_lift (b : T ⟶ sliceUnder (i ≫ p)) (c : T ⟶ sliceUnder (j ≫ p))
    (h : b ≫ sliceUnderRestrict (i ≫ p) f =
      c ≫ normalizedCoconeRestriction (j ≫ p) g (coconePushoutBoundary_eq hp p)) :
    ∃! a : T ⟶ sliceUnder p,
      a ≫ sliceUnderRestrict p i = b ∧ a ≫ sliceUnderRestrict p j = c := by
  have hh := congrArg sliceUnderUncurry h
  rw [sliceUnderUncurry_restrict, normalizedCoconeRestriction_uncurry] at hh
  let hs := join_left_isPushout hp T
  let H := hs.desc (sliceUnderUncurry b) (sliceUnderUncurry c) hh
  have hH : joinInl D T ≫ H = p := by
    apply hp.hom_ext
    · rw [← Category.assoc, ← joinInl_joinMap, Category.assoc, hs.inl_desc]
      exact sliceUnderUncurry_fixed b
    · rw [← Category.assoc, ← joinInl_joinMap, Category.assoc, hs.inr_desc]
      exact sliceUnderUncurry_fixed c
  let a := sliceUnderCurry H hH
  have ha : sliceUnderUncurry a = H := sliceUnderUncurry_curry _ _
  refine ⟨a, ⟨?_, ?_⟩, ?_⟩
  · apply sliceUnderUncurry_injective (i ≫ p)
    rw [sliceUnderUncurry_restrict, ha]
    exact hs.inl_desc _ _ _
  · apply sliceUnderUncurry_injective (j ≫ p)
    rw [sliceUnderUncurry_restrict, ha]
    exact hs.inr_desc _ _ _
  · intro m hm
    apply sliceUnderUncurry_injective p
    rw [ha]
    apply hs.hom_ext
    · rw [← sliceUnderUncurry_restrict, hm.1]
      exact (hs.inl_desc _ _ _).symm
    · rw [← sliceUnderUncurry_restrict, hm.2]
      exact (hs.inr_desc _ _ _).symm

/-- 形状の押し出し上の余錐の coslice は、二つの部分の coslice の厳密な引き戻し。 -/
lemma cosliceShapePushout_isPullback :
    IsPullback (sliceUnderRestrict p i) (sliceUnderRestrict p j)
      (sliceUnderRestrict (i ≫ p) f)
      (normalizedCoconeRestriction (j ≫ p) g (coconePushoutBoundary_eq hp p)) := by
  apply IsPullback.of_isLimit (c := PullbackCone.mk _ _ (cosliceShapePushout_comm hp p))
  apply PullbackCone.isLimitAux'
  intro s
  let h := cosliceShapePushout_lift hp p s.fst s.snd s.condition
  exact ⟨h.choose, h.choose_spec.1.1, h.choose_spec.1.2,
    fun {_} h₁ h₂ ↦ h.choose_spec.2 _ ⟨h₁, h₂⟩⟩

/-- 余錐全体の貼り合わせを、実際の単体集合の同型で表す。 -/
def cosliceShapePushoutIso :
    sliceUnder p ≅ pullback (sliceUnderRestrict (i ≫ p) f)
      (normalizedCoconeRestriction (j ≫ p) g (coconePushoutBoundary_eq hp p)) :=
  (cosliceShapePushout_isPullback hp p).isoPullback

end
end SerrePositivity.InfinityCategories.HomotopyLimits
