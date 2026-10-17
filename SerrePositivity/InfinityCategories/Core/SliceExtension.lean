module

public import SerrePositivity.InfinityCategories.Core.JoinBoundary

/-!
概要：slice 射影の持ち上げ性と端点を固定した join の延長性の比較。
方針：slice の普遍性と空 join の同型で、二種類の充填問題を直接往復する。
規約：quasicategory の仮定は不要。任意の単体集合と部分複体を扱う。
使われ方：HTT §1.2.12、Kerodon Corollary 4.7.3.12 の終対象の特徴づけ。
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Limits SSet
open scoped Simplicial

namespace SerrePositivity.InfinityCategories

/-- 概要：右端の図式を固定した pushout-join 上の射が全 join に延長できるという条件。
方針：空部分複体を右の部分複体として使い、左側の錐と頂点側の射を同時に指定する。
規約：任意の T と固定条件に対する延長の存在を表す Prop。
使われ方：HTT §1.2.12、Kerodon Corollary 4.7.3.12 の境界充填への移送。 -/
def SliceOverExtensionProperty {A K X : SSet.{u}} (A₀ : A.Subcomplex) (p : K ⟶ X) : Prop :=
  ∀ T : (joinUnion A₀ (⊥ : K.Subcomplex) : SSet.{u}) ⟶ X,
    joinInr (A₀ : SSet.{u}) K ≫ joinUnionLeft A₀ (⊥ : K.Subcomplex) ≫ T = p →
      ∃ L : join A K ⟶ X, (joinUnion A₀ (⊥ : K.Subcomplex)).ι ≫ L = T

/-- 概要：slice 射影の持ち上げ性から端点固定の join の延長性が従う。
方針：錐を curry し、自由因子上の射とともに射影の正方形を作り、持ち上げを uncurry する。
規約：任意の部分複体包含を試験射とする。
使われ方：HTT §1.2.12、Kerodon Corollary 4.7.3.12 の終対象からの逆方向。 -/
lemma sliceOverExtensionProperty_of_lifting {A K X : SSet.{u}}
    (A₀ : A.Subcomplex) (p : K ⟶ X) (h : HasLiftingProperty A₀.ι (sliceOverProjection p)) :
    SliceOverExtensionProperty A₀ p := by
  intro T hT
  let E : SSet.{u} := (⊥ : K.Subcomplex)
  let G := joinUnionLeft A₀ (⊥ : K.Subcomplex) ≫ T
  let H := joinUnionRight A₀ (⊥ : K.Subcomplex) ≫ T
  let b := (joinEmptyIso A K).inv ≫ H
  let hs := joinUnion_isPushout A₀ (⊥ : K.Subcomplex)
  have hover : joinMap (𝟙 (A₀ : SSet.{u})) (⊥ : K.Subcomplex).ι ≫ G =
      joinMap A₀.ι (𝟙 E) ≫ H := by
    dsimp [G, H]
    rw [← Category.assoc, ← Category.assoc, hs.w]
  have hbase : joinInl (A₀ : SSet.{u}) K ≫ G = A₀.ι ≫ b := by
    have hh := congrArg (fun z ↦ (joinEmptyIso (A₀ : SSet.{u}) K).inv ≫ z) hover
    rw [← Category.assoc, joinEmptyIso_inv, joinInl_joinMap, Category.id_comp] at hh
    rw [← Category.assoc (joinInl (A₀ : SSet.{u}) E) (joinMap A₀.ι (𝟙 E)) H,
      joinInl_joinMap, Category.assoc] at hh
    exact hh
  have hG : joinInr (A₀ : SSet.{u}) K ≫ G = p := hT
  have sq : CommSq (sliceOverCurry G hG) A₀.ι (sliceOverProjection p) b :=
    ⟨by rw [sliceOverCurry_projection]; exact hbase⟩
  have := h
  let L := sliceOverUncurry sq.lift
  have hleft : joinMap A₀.ι (𝟙 K) ≫ L = G := by
    have hh := congrArg sliceOverUncurry sq.fac_left
    rw [sliceOverUncurry_precomp, sliceOverUncurry_curry] at hh
    exact hh
  have hright : joinMap (𝟙 A) (⊥ : K.Subcomplex).ι ≫ L = H := by
    apply (cancel_epi (joinEmptyIso A K).inv).1
    rw [← Category.assoc, joinEmptyIso_inv, joinInl_joinMap, Category.id_comp]
    change joinInl A K ≫ sliceOverUncurry sq.lift = b
    rw [sliceOverUncurry_projection]
    exact sq.fac_right
  refine ⟨L, ?_⟩
  apply hs.hom_ext
  · rw [← Category.assoc, joinUnionLeft_ι]
    exact hleft
  · rw [← Category.assoc, joinUnionRight_ι]
    exact hright

/-- 概要：端点固定の join の延長性から slice 射影の持ち上げ性が従う。
方針：与えられた錐と自由因子上の射を貼り合わせ、延長を curry する。
規約：任意の部分複体包含を試験射とし、quasicategory 性を仮定しない。
使われ方：HTT §1.2.12、Kerodon Corollary 4.7.3.12 の終対象の充填性。 -/
lemma sliceOverProjection_lifting_of_extension {A K X : SSet.{u}}
    (A₀ : A.Subcomplex) (p : K ⟶ X) (h : SliceOverExtensionProperty A₀ p) :
    HasLiftingProperty A₀.ι (sliceOverProjection p) := by
  constructor
  intro a b sq
  let E : SSet.{u} := (⊥ : K.Subcomplex)
  let G := sliceOverUncurry a
  let H := (joinEmptyIso A K).hom ≫ b
  have hover : joinMap (𝟙 (A₀ : SSet.{u})) (⊥ : K.Subcomplex).ι ≫ G =
      joinMap A₀.ι (𝟙 E) ≫ H := by
    apply (cancel_epi (joinEmptyIso (A₀ : SSet.{u}) K).inv).1
    rw [← Category.assoc, joinEmptyIso_inv, joinInl_joinMap, Category.id_comp,
      ← Category.assoc, joinInl_joinMap, Category.assoc]
    change joinInl (A₀ : SSet.{u}) K ≫ G =
      A₀.ι ≫ ((joinEmptyIso A K).inv ≫ ((joinEmptyIso A K).hom ≫ b))
    rw [Iso.inv_hom_id_assoc, sliceOverUncurry_projection]
    exact sq.w
  let hs := joinUnion_isPushout A₀ (⊥ : K.Subcomplex)
  let T := hs.desc G H hover
  have hT : joinInr (A₀ : SSet.{u}) K ≫ joinUnionLeft A₀ (⊥ : K.Subcomplex) ≫ T = p := by
    rw [hs.inl_desc]
    exact sliceOverUncurry_fixed a
  obtain ⟨L, hL⟩ := h T hT
  have hleft : joinMap A₀.ι (𝟙 K) ≫ L = G := by
    rw [← joinUnionLeft_ι, Category.assoc, hL]
    exact hs.inl_desc G H hover
  have hright : joinMap (𝟙 A) (⊥ : K.Subcomplex).ι ≫ L = H := by
    rw [← joinUnionRight_ι, Category.assoc, hL]
    exact hs.inr_desc G H hover
  have hfixed : joinInr A K ≫ L = p := by
    have hh := congrArg (fun z ↦ joinInr (A₀ : SSet.{u}) K ≫ z) hleft
    rw [← Category.assoc, joinInr_joinMap, Category.id_comp] at hh
    exact hh.trans (sliceOverUncurry_fixed a)
  refine CommSq.HasLift.mk' { l := sliceOverCurry L hfixed, fac_left := ?_, fac_right := ?_ }
  · apply sliceOverUncurry_injective p
    rw [sliceOverUncurry_precomp, sliceOverUncurry_curry]
    exact hleft
  · rw [sliceOverCurry_projection]
    have hh := congrArg (fun z ↦ (joinEmptyIso A K).inv ≫ z) hright
    rw [← Category.assoc, joinEmptyIso_inv, joinInl_joinMap, Category.id_comp] at hh
    exact hh.trans (by dsimp [H]; rw [← joinEmptyIso_inv, Iso.inv_hom_id_assoc])

/-- 概要：左端の図式を固定した pushout-join 上の射が全 join に延長できるという条件。
方針：空部分複体を左の部分複体として使い、右側の錐と頂点側の射を同時に指定する。
規約：任意の T と固定条件に対する延長の存在を表す Prop。
使われ方：HTT §1.2.12、Kerodon Corollary 4.7.3.12 の境界充填への移送。 -/
def SliceUnderExtensionProperty {A K X : SSet.{u}} (A₀ : A.Subcomplex) (p : K ⟶ X) : Prop :=
  ∀ T : (joinUnion (⊥ : K.Subcomplex) A₀ : SSet.{u}) ⟶ X,
    joinInl K (A₀ : SSet.{u}) ≫ joinUnionRight (⊥ : K.Subcomplex) A₀ ≫ T = p →
      ∃ L : join K A ⟶ X, (joinUnion (⊥ : K.Subcomplex) A₀).ι ≫ L = T

/-- 概要：coslice 射影の持ち上げ性から端点固定の join の延長性が従う。
方針：錐を curry し、自由因子上の射とともに射影の正方形を作り、持ち上げを uncurry する。
規約：任意の部分複体包含を試験射とする。
使われ方：HTT §1.2.12、Kerodon Corollary 4.7.3.12 の終対象からの逆方向。 -/
lemma sliceUnderExtensionProperty_of_lifting {A K X : SSet.{u}}
    (A₀ : A.Subcomplex) (p : K ⟶ X) (h : HasLiftingProperty A₀.ι (sliceUnderProjection p)) :
    SliceUnderExtensionProperty A₀ p := by
  intro T hT
  let E : SSet.{u} := (⊥ : K.Subcomplex)
  let G := joinUnionRight (⊥ : K.Subcomplex) A₀ ≫ T
  let H := joinUnionLeft (⊥ : K.Subcomplex) A₀ ≫ T
  let b := (emptyJoinIso K A).inv ≫ H
  let hs := (joinUnion_isPushout (⊥ : K.Subcomplex) A₀).flip
  have hover : joinMap (⊥ : K.Subcomplex).ι (𝟙 (A₀ : SSet.{u})) ≫ G =
      joinMap (𝟙 E) A₀.ι ≫ H := by
    dsimp [G, H]
    rw [← Category.assoc, ← Category.assoc, hs.w]
  have hbase : joinInr K (A₀ : SSet.{u}) ≫ G = A₀.ι ≫ b := by
    have hh := congrArg (fun z ↦ (emptyJoinIso K (A₀ : SSet.{u})).inv ≫ z) hover
    rw [← Category.assoc, emptyJoinIso_inv, joinInr_joinMap, Category.id_comp] at hh
    rw [← Category.assoc (joinInr E (A₀ : SSet.{u})) (joinMap (𝟙 E) A₀.ι) H,
      joinInr_joinMap, Category.assoc] at hh
    exact hh
  have hG : joinInl K (A₀ : SSet.{u}) ≫ G = p := hT
  have sq : CommSq (sliceUnderCurry G hG) A₀.ι (sliceUnderProjection p) b :=
    ⟨by rw [sliceUnderCurry_projection]; exact hbase⟩
  have := h
  let L := sliceUnderUncurry sq.lift
  have hleft : joinMap (𝟙 K) A₀.ι ≫ L = G := by
    have hh := congrArg sliceUnderUncurry sq.fac_left
    rw [sliceUnderUncurry_precomp, sliceUnderUncurry_curry] at hh
    exact hh
  have hright : joinMap (⊥ : K.Subcomplex).ι (𝟙 A) ≫ L = H := by
    apply (cancel_epi (emptyJoinIso K A).inv).1
    rw [← Category.assoc, emptyJoinIso_inv, joinInr_joinMap, Category.id_comp]
    change joinInr K A ≫ sliceUnderUncurry sq.lift = b
    rw [sliceUnderUncurry_projection]
    exact sq.fac_right
  refine ⟨L, ?_⟩
  apply hs.hom_ext
  · rw [← Category.assoc, joinUnionRight_ι]
    exact hleft
  · rw [← Category.assoc, joinUnionLeft_ι]
    exact hright

/-- 概要：端点固定の join の延長性から coslice 射影の持ち上げ性が従う。
方針：与えられた錐と自由因子上の射を貼り合わせ、延長を curry する。
規約：任意の部分複体包含を試験射とし、quasicategory 性を仮定しない。
使われ方：HTT §1.2.12、Kerodon Corollary 4.7.3.12 の終対象の充填性。 -/
lemma sliceUnderProjection_lifting_of_extension {A K X : SSet.{u}}
    (A₀ : A.Subcomplex) (p : K ⟶ X) (h : SliceUnderExtensionProperty A₀ p) :
    HasLiftingProperty A₀.ι (sliceUnderProjection p) := by
  constructor
  intro a b sq
  let E : SSet.{u} := (⊥ : K.Subcomplex)
  let G := sliceUnderUncurry a
  let H := (emptyJoinIso K A).hom ≫ b
  have hover : joinMap (⊥ : K.Subcomplex).ι (𝟙 (A₀ : SSet.{u})) ≫ G =
      joinMap (𝟙 E) A₀.ι ≫ H := by
    apply (cancel_epi (emptyJoinIso K (A₀ : SSet.{u})).inv).1
    rw [← Category.assoc, emptyJoinIso_inv, joinInr_joinMap, Category.id_comp,
      ← Category.assoc, joinInr_joinMap, Category.assoc]
    change joinInr K (A₀ : SSet.{u}) ≫ G =
      A₀.ι ≫ ((emptyJoinIso K A).inv ≫ ((emptyJoinIso K A).hom ≫ b))
    rw [Iso.inv_hom_id_assoc, sliceUnderUncurry_projection]
    exact sq.w
  let hs := (joinUnion_isPushout (⊥ : K.Subcomplex) A₀).flip
  let T := hs.desc G H hover
  have hT : joinInl K (A₀ : SSet.{u}) ≫ joinUnionRight (⊥ : K.Subcomplex) A₀ ≫ T = p := by
    rw [hs.inl_desc]
    exact sliceUnderUncurry_fixed a
  obtain ⟨L, hL⟩ := h T hT
  have hleft : joinMap (𝟙 K) A₀.ι ≫ L = G := by
    rw [← joinUnionRight_ι, Category.assoc, hL]
    exact hs.inl_desc G H hover
  have hright : joinMap (⊥ : K.Subcomplex).ι (𝟙 A) ≫ L = H := by
    rw [← joinUnionLeft_ι, Category.assoc, hL]
    exact hs.inr_desc G H hover
  have hfixed : joinInl K A ≫ L = p := by
    have hh := congrArg (fun z ↦ joinInl K (A₀ : SSet.{u}) ≫ z) hleft
    rw [← Category.assoc, joinInl_joinMap, Category.id_comp] at hh
    exact hh.trans (sliceUnderUncurry_fixed a)
  refine CommSq.HasLift.mk' { l := sliceUnderCurry L hfixed, fac_left := ?_, fac_right := ?_ }
  · apply sliceUnderUncurry_injective p
    rw [sliceUnderUncurry_precomp, sliceUnderUncurry_curry]
    exact hleft
  · rw [sliceUnderCurry_projection]
    have hh := congrArg (fun z ↦ (emptyJoinIso K A).inv ≫ z) hright
    rw [← Category.assoc, emptyJoinIso_inv, joinInr_joinMap, Category.id_comp] at hh
    exact hh.trans (by dsimp [H]; rw [← emptyJoinIso_inv, Iso.inv_hom_id_assoc])

end SerrePositivity.InfinityCategories
