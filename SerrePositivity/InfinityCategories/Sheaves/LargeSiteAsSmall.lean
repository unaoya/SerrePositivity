module

public import SerrePositivity.InfinityCategories.Sheaves.AsSmallSiteInvariance
public import SerrePositivity.InfinityCategories.Sheaves.SiteSmallModelShape

/-!
概要：本質的小さい大きい site の元の前層と全被覆篩を、同じ宇宙の AsSmall 表示で扱う。
方針：元の nerve の厳密な同型と、通常圏の同値による篩の順像・逆像を用いる。
  文献対応：HTT 6.2.2.6、Kerodon §4.5.1（Tag 01DQ）の小さい模型への置き換え。
規約：対象 Type(u+1)・射 Type u・係数 SSet(u+1)。κの切り落としを新設しない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory CategoryTheory.Functor SSet
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
namespace SerrePositivity.InfinityCategories.Sheaves

/-- 対象・射の宇宙が異なる場合も、AsSmall の逆への篩の順像は元の順射への逆像。 -/
lemma asSmall_functorPushforward_down_general {C : Type u} [Category.{v} C] {U : C}
    (S : Sieve ((AsSmall.up : C ⥤ AsSmall.{w} C).obj U)) :
    S.functorPushforward AsSmall.down = S.functorPullback AsSmall.up := by
  let e : C ≌ AsSmall.{w} C := AsSmall.equiv
  have h := Sieve.functorPushforward_inverse S e
  change S.functorPushforward AsSmall.down =
    (S.pullback (𝟙 (AsSmall.up.obj U))).functorPullback AsSmall.up at h
  simpa only [Sieve.pullback_id] using h

/-- 同じ AsSmall の全射で、元の篩を逆像・順像により厳密に回収する。 -/
lemma asSmall_functorPushforward_functorPullback {C : Type u} [Category.{v} C] {U : C}
    (S : Sieve ((AsSmall.up : C ⥤ AsSmall.{w} C).obj U)) :
    (S.functorPullback AsSmall.up).functorPushforward AsSmall.up = S := by
  let e : C ≌ AsSmall.{w} C := AsSmall.equiv
  have h := Sieve.functorPushforward_equivalence_eq_pullback e.symm S
  change (S.functorPushforward AsSmall.down).functorPushforward AsSmall.up =
    S.pullback (𝟙 (AsSmall.up.obj U)) at h
  rw [asSmall_functorPushforward_down_general, Sieve.pullback_id] at h
  exact h

variable {C : Type (u + 1)} [Category.{u} C]
variable {E : SSet.{u + 1}} [Quasicategory E]

/-- 元の大きい site の nerve と同じ宇宙の AsSmall 表示の厳密な同型。 -/
def largeSiteShapeIso (C : Type (u + 1)) [Category.{u} C] :
    nerve Cᵒᵖ ≅ nerve (AsSmall.{u + 1} C)ᵒᵖ where
  hom :=
    { app := fun _ ↦ ↾fun σ ↦ σ ⋙ AsSmall.up.op
      naturality := fun _ _ _ ↦ rfl }
  inv :=
    { app := fun _ ↦ ↾fun σ ↦ σ ⋙ AsSmall.down.op
      naturality := fun _ _ _ ↦ rfl }
  hom_inv_id := rfl
  inv_hom_id := rfl

/-- 元の全前層を、同じ係数の AsSmall 表示へ移す。 -/
def asSmallLargePresheaf (F : nerve Cᵒᵖ ⟶ E) : nerve (AsSmall.{u + 1} C)ᵒᵖ ⟶ E :=
  (largeSiteShapeIso C).inv ≫ F

/-- 元の大きい site の層条件。同じ宇宙の全被覆篩の指定錐による表示。 -/
def LargeIsSheaf (J : GrothendieckTopology C) (F : nerve Cᵒᵖ ⟶ E) : Prop :=
  NativeIsSheaf ((AsSmall.down : AsSmall.{u + 1} C ⥤ C).inducedTopology J)
    (asSmallLargePresheaf F)

/-- AsSmall 表示の被覆篩であることは、元の同じ逆像の篩の被覆性と一致する。 -/
lemma mem_largeAsSmallTopology_iff (J : GrothendieckTopology C) {U : C}
    (S : Sieve ((AsSmall.up : C ⥤ AsSmall.{u + 1} C).obj U)) :
    S ∈ (AsSmall.down : AsSmall.{u + 1} C ⥤ C).inducedTopology J (AsSmall.up.obj U) ↔
      S.functorPullback AsSmall.up ∈ J U := by
  letI : (AsSmall.down : AsSmall.{u + 1} C ⥤ C).IsEquivalence :=
    (AsSmall.equiv (C := C)).isEquivalence_inverse
  rw [mem_inducedTopology_iff_of_isCoverDense, asSmall_functorPushforward_down_general]
  rfl

/-- 元の篩 S の全射を保つ AsSmall 表示の、元の前層 F の指定制限錐。 -/
def largeRestrictionCone (F : nerve Cᵒᵖ ⟶ E) {U : C} (S : Sieve U) :
    JoinCone (nativeRestriction (asSmallLargePresheaf F)
      (S.functorPushforward (AsSmall.up : C ⥤ AsSmall.{u + 1} C))) :=
  nativeRestrictionCone (asSmallLargePresheaf F) (S.functorPushforward AsSmall.up)

/-- 大きい site の表示は、元のすべての被覆篩の指定錐の極限性そのものである。 -/
theorem largeIsSheaf_iff_original_coveringCones (J : GrothendieckTopology C)
    (F : nerve Cᵒᵖ ⟶ E) :
    LargeIsSheaf J F ↔ ∀ (U : C) (S : Sieve U), S ∈ J U →
      IsLimitCone (largeRestrictionCone F S) := by
  letI : (AsSmall.up : C ⥤ AsSmall.{u + 1} C).IsEquivalence :=
    (AsSmall.equiv (C := C)).isEquivalence_functor
  constructor
  · intro h U S hS
    have he : (S.functorPushforward AsSmall.up).functorPullback AsSmall.up = S :=
      Sieve.functorPullback_functorPushforward_eq AsSmall.up
    have hT := (mem_largeAsSmallTopology_iff J (S.functorPushforward AsSmall.up)).mpr
      (he.symm ▸ hS)
    exact h _ _ hT
  · intro h V S hS
    rcases V with ⟨U⟩
    have hR := (mem_largeAsSmallTopology_iff J S).mp hS
    have hL := h U (S.functorPullback AsSmall.up) hR
    change IsLimitCone (nativeRestrictionCone (asSmallLargePresheaf F)
      ((S.functorPullback AsSmall.up).functorPushforward AsSmall.up)) at hL
    rw [asSmall_functorPushforward_functorPullback] at hL
    exact hL

end SerrePositivity.InfinityCategories.Sheaves
