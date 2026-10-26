module

public import SerrePositivity.InfinityCategories.Stable.RightJoinCoproduct
public import SerrePositivity.InfinityCategories.HomotopyLimits.IteratedSliceOverRestriction
public import SerrePositivity.InfinityCategories.Core.InnerFiber

/-!
概要：二つの固定図式上の実 slice は、同じ始域上の厳密な引き戻しをなす。
方針：任意パラメータとの join の実 pushout で全錐族を貼り合わせる。
規約：終点・全図式・全パラメータを保持し、quasicategory 性を要求しない。
使われ方：実分母・次辺族を、二終点上の単一の実 slice へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.InfinityCategories.HomotopyLimits
namespace SerrePositivity.KST.LocalizingInvariants
variable {U V X : SSet.{u}} (p : U ⟶ X) (q : V ⟶ X)

/-- 二図式上の実錐を、左の同じ元の図式へ制限する。 -/
def sliceOverCoproductLeft : sliceOver (coprod.desc p q) ⟶ sliceOver p :=
  sliceOverRestrict (coprod.desc p q) coprod.inl ≫
    eqToHom (congrArg (fun f : U ⟶ X => sliceOver f) (coprod.inl_desc p q))

/-- 二図式上の実錐を、右の同じ元の図式へ制限する。 -/
def sliceOverCoproductRight : sliceOver (coprod.desc p q) ⟶ sliceOver q :=
  sliceOverRestrict (coprod.desc p q) coprod.inr ≫
    eqToHom (congrArg (fun f : V ⟶ X => sliceOver f) (coprod.inr_desc p q))

lemma sliceOverCoproductLeft_uncurry {T : SSet.{u}}
    (F : T ⟶ sliceOver (coprod.desc p q)) :
    sliceOverUncurry (F ≫ sliceOverCoproductLeft p q) =
      joinMap (𝟙 T) coprod.inl ≫ sliceOverUncurry F := by
  rw [sliceOverCoproductLeft, ← Category.assoc, sliceOverUncurry_eqToHom,
    sliceOverUncurry_restrict]
  exact coprod.inl_desc p q

lemma sliceOverCoproductRight_uncurry {T : SSet.{u}}
    (F : T ⟶ sliceOver (coprod.desc p q)) :
    sliceOverUncurry (F ≫ sliceOverCoproductRight p q) =
      joinMap (𝟙 T) coprod.inr ≫ sliceOverUncurry F := by
  rw [sliceOverCoproductRight, ← Category.assoc, sliceOverUncurry_eqToHom,
    sliceOverUncurry_restrict]
  exact coprod.inr_desc p q

lemma sliceOverCoproductLeft_vertex_val (c : JoinCone (coprod.desc p q)) :
    ((sliceOverCoproductLeft p q).app (Opposite.op ⦋0⦌) c).val =
      joinMap (𝟙 (Δ[0] : SSet.{u})) coprod.inl ≫ c.val := by
  have h := sliceOverCoproductLeft_uncurry p q (SSet.yonedaEquiv.symm c)
  rw [SSet.yonedaEquiv_symm_comp, sliceOverUncurry_yoneda, sliceOverUncurry_yoneda] at h
  exact h

lemma sliceOverCoproductLeft_projection :
    sliceOverCoproductLeft p q ≫ sliceOverProjection p =
      sliceOverProjection (coprod.desc p q) := by
  rw [← sliceOverUncurry_projection]
  have h := sliceOverCoproductLeft_uncurry p q (𝟙 _)
  rw [Category.id_comp] at h
  rw [h, ← Category.assoc, joinInl_joinMap, Category.id_comp,
    sliceOverUncurry_projection, Category.id_comp]

lemma sliceOverCoproductRight_projection :
    sliceOverCoproductRight p q ≫ sliceOverProjection q =
      sliceOverProjection (coprod.desc p q) := by
  rw [← sliceOverUncurry_projection]
  have h := sliceOverCoproductRight_uncurry p q (𝟙 _)
  rw [Category.id_comp] at h
  rw [h, ← Category.assoc, joinInl_joinMap, Category.id_comp,
    sliceOverUncurry_projection, Category.id_comp]

/-- 同じ始域を持つ二つの元の全錐族を、二図式上の一つの全錐族へ貼る。 -/
def sliceOverCoproductGlue {T : SSet.{u}} (a : T ⟶ sliceOver p) (b : T ⟶ sliceOver q)
    (h : a ≫ sliceOverProjection p = b ≫ sliceOverProjection q) :
    T ⟶ sliceOver (coprod.desc p q) := by
  let hp := join_right_coproduct_isPushout U V T
  have hab : joinInl T U ≫ sliceOverUncurry a =
      joinInl T V ≫ sliceOverUncurry b := by
    rw [sliceOverUncurry_projection, sliceOverUncurry_projection, h]
  let L := hp.desc (sliceOverUncurry a) (sliceOverUncurry b) hab
  have hL : joinInr T (U ⨿ V) ≫ L = coprod.desc p q := by
    apply coprod.hom_ext
    · rw [← Category.assoc, ← joinInr_joinMap (𝟙 T) (coprod.inl : U ⟶ U ⨿ V),
        Category.assoc]
      rw [show joinMap (𝟙 T) coprod.inl ≫ L = sliceOverUncurry a from hp.inl_desc _ _ _,
        sliceOverUncurry_fixed, coprod.inl_desc]
    · rw [← Category.assoc, ← joinInr_joinMap (𝟙 T) (coprod.inr : V ⟶ U ⨿ V),
        Category.assoc]
      rw [show joinMap (𝟙 T) coprod.inr ≫ L = sliceOverUncurry b from hp.inr_desc _ _ _,
        sliceOverUncurry_fixed, coprod.inr_desc]
  exact sliceOverCurry L hL

lemma sliceOverCoproductGlue_left {T : SSet.{u}} (a : T ⟶ sliceOver p) (b : T ⟶ sliceOver q)
    (h : a ≫ sliceOverProjection p = b ≫ sliceOverProjection q) :
    sliceOverCoproductGlue p q a b h ≫ sliceOverCoproductLeft p q = a := by
  apply sliceOverUncurry_injective p
  rw [sliceOverCoproductLeft_uncurry, sliceOverCoproductGlue, sliceOverUncurry_curry]
  exact (join_right_coproduct_isPushout U V T).inl_desc _ _ _

lemma sliceOverCoproductGlue_right {T : SSet.{u}} (a : T ⟶ sliceOver p) (b : T ⟶ sliceOver q)
    (h : a ≫ sliceOverProjection p = b ≫ sliceOverProjection q) :
    sliceOverCoproductGlue p q a b h ≫ sliceOverCoproductRight p q = b := by
  apply sliceOverUncurry_injective q
  rw [sliceOverCoproductRight_uncurry, sliceOverCoproductGlue, sliceOverUncurry_curry]
  exact (join_right_coproduct_isPushout U V T).inr_desc _ _ _

/-- 二図式上の元の実 slice は、二つの同じ実始域射影の厳密な引き戻し。 -/
lemma isPullback_sliceOverCoproduct :
    IsPullback (sliceOverCoproductRight p q) (sliceOverCoproductLeft p q)
      (sliceOverProjection q) (sliceOverProjection p) := by
  apply IsPullback.mk'
    (by rw [sliceOverCoproductRight_projection, sliceOverCoproductLeft_projection])
  · intro T a b ha hb
    apply sliceOverUncurry_injective (coprod.desc p q)
    apply (join_right_coproduct_isPushout U V T).hom_ext
    · rw [← sliceOverCoproductLeft_uncurry, ← sliceOverCoproductLeft_uncurry, hb]
    · rw [← sliceOverCoproductRight_uncurry, ← sliceOverCoproductRight_uncurry, ha]
  · intro T a b h
    exact ⟨sliceOverCoproductGlue p q b a h.symm,
      sliceOverCoproductGlue_right p q b a h.symm,
      sliceOverCoproductGlue_left p q b a h.symm⟩

/-- 二終点上の実 slice と、同じ始域を共有する二つの実 slice の厳密同型。 -/
def sliceOverCoproductIso : sliceOver (coprod.desc p q) ≅
    pullback (sliceOverProjection q) (sliceOverProjection p) :=
  (isPullback_sliceOverCoproduct p q).isoPullback

end SerrePositivity.KST.LocalizingInvariants
