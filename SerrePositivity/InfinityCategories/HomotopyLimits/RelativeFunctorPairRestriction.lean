module

public import SerrePositivity.InfinityCategories.HomotopyLimits.RelativeFunctorCoprodPair
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorRestrictionFibration

/-!
概要：互いに交わらない二部分の同時制限を、余積形状への制限で構成する。
方針：両枝の raw な族を貼り、余積包含による制限の持ち上げを使う。
規約：結合した包含の単射性を明示する。使われ方：初期値固定の終点評価の充填性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
attribute [local irreducible] relativeFunctorCurry relativeFunctorUncurry
variable {A D C E B : SSet.{u}} (p : E ⟶ B) (β : A ⟶ B) (i : D ⟶ A) (j : C ⟶ A)

/-- 二部分の相対族を、同じ底を保って同時に制限する。 -/
def relativeFunctorPairRestriction : relativeFunctorSpace p β ⟶
    relativeFunctorSpace p (i ≫ β) ⊗ relativeFunctorSpace p (j ≫ β) :=
  lift (relativeFunctorPre p β i) (relativeFunctorPre p β j)

/-- 余積形状への制限が持ち上げる射は、二部分の同時制限でも持ち上げる。 -/
lemma relativeFunctorPairRestriction_hasLiftingProperty {T U : SSet.{u}} (r : T ⟶ U)
    [HasLiftingProperty r (relativeFunctorPre p β (coprod.desc i j))] :
    HasLiftingProperty r (relativeFunctorPairRestriction p β i j) := by
  constructor
  intro a b sq
  let m := coprod.desc i j
  let G := coprodTensorGlue (relativeFunctorUncurry (b ≫ fst _ _))
    (relativeFunctorUncurry (b ≫ snd _ _))
  have hG : G ≫ p = fst (D ⨿ C) U ≫ (m ≫ β) := by
    apply coprodTensor_hom_ext
    · rw [← Category.assoc, coprodTensorGlue_inl, relativeFunctorUncurry_projection,
        whiskerRight_fst_assoc, ← Category.assoc coprod.inl, coprod.inl_desc]
    · rw [← Category.assoc, coprodTensorGlue_inr, relativeFunctorUncurry_projection,
        whiskerRight_fst_assoc, ← Category.assoc coprod.inr, coprod.inr_desc]
  let b' := relativeFunctorCurry G hG
  have h₀ : (coprod.inl ▷ U) ≫ relativeFunctorUncurry b' =
      relativeFunctorUncurry (b ≫ fst _ _) := by
    rw [relativeFunctorUncurry_curry, coprodTensorGlue_inl]
  have h₁ : (coprod.inr ▷ U) ≫ relativeFunctorUncurry b' =
      relativeFunctorUncurry (b ≫ snd _ _) := by
    rw [relativeFunctorUncurry_curry, coprodTensorGlue_inr]
  have ha₀ : a ≫ relativeFunctorPre p β i = r ≫ (b ≫ fst _ _) := by
    simpa only [relativeFunctorPairRestriction, Category.assoc, lift_fst] using
      congrArg (fun t ↦ t ≫ fst _ _) sq.w
  have ha₁ : a ≫ relativeFunctorPre p β j = r ≫ (b ≫ snd _ _) := by
    simpa only [relativeFunctorPairRestriction, Category.assoc, lift_snd] using
      congrArg (fun t ↦ t ≫ snd _ _) sq.w
  have hs : CommSq a r (relativeFunctorPre p β m) b' := by
    constructor
    apply relativeFunctorUncurry_injective p (m ≫ β)
    apply coprodTensor_hom_ext
    · calc
        _ = (i ▷ T) ≫ relativeFunctorUncurry a := by
          rw [relativeFunctorUncurry_pre, ← Category.assoc,
            ← MonoidalCategory.comp_whiskerRight, coprod.inl_desc]
        _ = relativeFunctorUncurry (a ≫ relativeFunctorPre p β i) :=
          (relativeFunctorUncurry_pre a i).symm
        _ = relativeFunctorUncurry (r ≫ (b ≫ fst _ _)) := congrArg relativeFunctorUncurry ha₀
        _ = (D ◁ r) ≫ relativeFunctorUncurry (b ≫ fst _ _) :=
          SerrePositivity.InfinityCategories.relativeFunctorUncurry_parameter (b ≫ fst _ _) r
        _ = _ := by
          rw [SerrePositivity.InfinityCategories.relativeFunctorUncurry_parameter b' r,
            ← Category.assoc, ← whisker_exchange,
            Category.assoc, h₀]
    · calc
        _ = (j ▷ T) ≫ relativeFunctorUncurry a := by
          rw [relativeFunctorUncurry_pre, ← Category.assoc,
            ← MonoidalCategory.comp_whiskerRight, coprod.inr_desc]
        _ = relativeFunctorUncurry (a ≫ relativeFunctorPre p β j) :=
          (relativeFunctorUncurry_pre a j).symm
        _ = relativeFunctorUncurry (r ≫ (b ≫ snd _ _)) := congrArg relativeFunctorUncurry ha₁
        _ = (C ◁ r) ≫ relativeFunctorUncurry (b ≫ snd _ _) :=
          SerrePositivity.InfinityCategories.relativeFunctorUncurry_parameter (b ≫ snd _ _) r
        _ = _ := by
          rw [SerrePositivity.InfinityCategories.relativeFunctorUncurry_parameter b' r,
            ← Category.assoc, ← whisker_exchange,
            Category.assoc, h₁]
  refine CommSq.HasLift.mk' { l := hs.lift, fac_left := hs.fac_left, fac_right := ?_ }
  apply CartesianMonoidalCategory.hom_ext
  · change hs.lift ≫ relativeFunctorPairRestriction p β i j ≫ fst _ _ = b ≫ fst _ _
    rw [relativeFunctorPairRestriction, lift_fst]
    apply relativeFunctorUncurry_injective p (i ≫ β)
    have h := congrArg (fun t ↦ (coprod.inl ▷ U) ≫ t)
      (congrArg relativeFunctorUncurry hs.fac_right)
    rw [relativeFunctorUncurry_pre, ← Category.assoc,
      ← MonoidalCategory.comp_whiskerRight, coprod.inl_desc, h₀] at h
    exact (relativeFunctorUncurry_pre hs.lift i).trans h
  · change hs.lift ≫ relativeFunctorPairRestriction p β i j ≫ snd _ _ = b ≫ snd _ _
    rw [relativeFunctorPairRestriction, lift_snd]
    apply relativeFunctorUncurry_injective p (j ≫ β)
    have h := congrArg (fun t ↦ (coprod.inr ▷ U) ≫ t)
      (congrArg relativeFunctorUncurry hs.fac_right)
    rw [relativeFunctorUncurry_pre, ← Category.assoc,
      ← MonoidalCategory.comp_whiskerRight, coprod.inr_desc, h₁] at h
    exact (relativeFunctorUncurry_pre hs.lift j).trans h

/-- 結合した包含が単射なら、二部分の同時制限は left fibration である。 -/
instance relativeFunctorPairRestriction_leftFibration [LeftFibration p]
    [Mono (coprod.desc i j)] : LeftFibration (relativeFunctorPairRestriction p β i j) where
  mem := by
    intro T U r hr
    have := LeftFibration.mem (p := relativeFunctorPre p β (coprod.desc i j)) r hr
    exact relativeFunctorPairRestriction_hasLiftingProperty p β i j r

end
end SerrePositivity.InfinityCategories.HomotopyLimits
