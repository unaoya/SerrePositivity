module

public import SerrePositivity.InfinityCategories.Core.FibrationRestriction

/-!
概要：inner fibration の相対 coslice 制限。
方針：標的の錐と部分図式の持ち上げを引き戻しにまとめ、pushout-join で延長する。
規約：制限する部分図式は任意の部分複体。
使われ方：HTT §2.1.2、Kerodon §4.4.2 の相対外側ホーン充填。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：相対 coslice 制限の標的。
方針：標的での錐と部分図式上の持ち上げの一致を引き戻しで表す。
規約：第一成分は始域での部分図式上の錐。
使われ方：HTT §2.1.2、Kerodon §4.4.2 の相対的な持ち上げ。 -/
noncomputable def relativeCosliceTarget {K X Y : SSet.{u}} (p : K ⟶ X) (q : X ⟶ Y)
    (K₀ : K.Subcomplex) : SSet.{u} :=
  pullback (sliceUnderPostcomp (K₀.ι ≫ p) q) (sliceUnderRestrict (p ≫ q) K₀.ι)

/-- 概要：coslice の相対制限の射。
方針：部分図式への制限と標的への後合成を組にする。
規約：両成分は制限と後合成の可換性で一致する。
使われ方：HTT §2.1.2、Kerodon §4.4.2 の相対制限。 -/
noncomputable def relativeCosliceMap {K X Y : SSet.{u}} (p : K ⟶ X) (q : X ⟶ Y)
    (K₀ : K.Subcomplex) : sliceUnder p ⟶ relativeCosliceTarget p q K₀ :=
  pullback.lift (sliceUnderRestrict p K₀.ι) (sliceUnderPostcomp p q)
    (sliceUnderRestrict_postcomp p K₀.ι q).symm

/-- 概要：相対 coslice 制限は左 anodyne な部分複体包含を持ち上げる。
方針：二つの錐を pushout-join に貼り、inner fibration の持ち上げを使う。
規約：quasicategory 性を仮定せず、射 q の inner fibration 性を使う。
使われ方：HTT §2.1.2、Kerodon §4.4.2 の相対的な補題。 -/
lemma relativeCosliceMap_hasLiftingProperty {A K X Y : SSet.{u}}
    (p : K ⟶ X) (q : X ⟶ Y) [InnerFibration q]
    (A₀ : A.Subcomplex) (K₀ : K.Subcomplex) (hA : leftAnodyneExtensions A₀.ι) :
    HasLiftingProperty A₀.ι (relativeCosliceMap p q K₀) := by
  constructor
  intro a b sq
  let r := pullback.fst (sliceUnderPostcomp (K₀.ι ≫ p) q)
    (sliceUnderRestrict (p ≫ q) K₀.ι)
  let s := pullback.snd (sliceUnderPostcomp (K₀.ι ≫ p) q)
    (sliceUnderRestrict (p ≫ q) K₀.ι)
  let G := sliceUnderUncurry a
  let H := sliceUnderUncurry (b ≫ r)
  let B := sliceUnderUncurry (b ≫ s)
  have ha : a ≫ sliceUnderRestrict p K₀.ι = A₀.ι ≫ (b ≫ r) := by
    have h := congrArg (fun f ↦ f ≫ r) sq.w
    simpa only [r, relativeCosliceMap, Category.assoc, pullback.lift_fst] using h
  have hb : a ≫ sliceUnderPostcomp p q = A₀.ι ≫ (b ≫ s) := by
    have h := congrArg (fun f ↦ f ≫ s) sq.w
    simpa only [s, relativeCosliceMap, Category.assoc, pullback.lift_snd] using h
  have hover : joinMap K₀.ι (𝟙 (A₀ : SSet.{u})) ≫ G =
      joinMap (𝟙 (K₀ : SSet.{u})) A₀.ι ≫ H := by
    have h := congrArg sliceUnderUncurry ha
    rw [sliceUnderUncurry_restrict, sliceUnderUncurry_precomp] at h
    exact h
  let hs := joinUnion_isPushout K₀ A₀
  let T := hs.desc H G hover.symm
  have hTB : T ≫ q = (joinUnion K₀ A₀).ι ≫ B := by
    apply hs.hom_ext
    · rw [← Category.assoc, hs.inl_desc, ← Category.assoc, joinUnionLeft_ι]
      have h : (b ≫ r) ≫ sliceUnderPostcomp (K₀.ι ≫ p) q =
          (b ≫ s) ≫ sliceUnderRestrict (p ≫ q) K₀.ι := by
        simpa only [r, s, Category.assoc] using congrArg (fun z ↦ b ≫ z)
          (pullback.condition (f := sliceUnderPostcomp (K₀.ι ≫ p) q)
            (g := sliceUnderRestrict (p ≫ q) K₀.ι))
      have hh := congrArg sliceUnderUncurry h
      rw [sliceUnderUncurry_postcomp, sliceUnderUncurry_restrict] at hh
      exact hh
    · rw [← Category.assoc, hs.inr_desc, ← Category.assoc, joinUnionRight_ι]
      have h := congrArg sliceUnderUncurry hb
      rw [sliceUnderUncurry_postcomp, sliceUnderUncurry_precomp] at h
      exact h
  have := joinUnion_innerAnodyne_of_leftAnodyne K₀ A₀ hA q (InnerFibration.mem (q := q))
  let hT : CommSq T (joinUnion K₀ A₀).ι q B := ⟨hTB⟩
  let L := hT.lift
  have hleft : joinMap K₀.ι (𝟙 A) ≫ L = H := by
    rw [← joinUnionLeft_ι, Category.assoc]
    change joinUnionLeft K₀ A₀ ≫ ((joinUnion K₀ A₀).ι ≫ hT.lift) = H
    rw [hT.fac_left]
    exact hs.inl_desc _ _ _
  have hright : joinMap (𝟙 K) A₀.ι ≫ L = G := by
    rw [← joinUnionRight_ι, Category.assoc]
    change joinUnionRight K₀ A₀ ≫ ((joinUnion K₀ A₀).ι ≫ hT.lift) = G
    rw [hT.fac_left]
    exact hs.inr_desc _ _ _
  have hfixed : joinInl K A ≫ L = p := by
    have h := congrArg (fun z ↦ joinInl K (A₀ : SSet.{u}) ≫ z) hright
    rw [← Category.assoc, joinInl_joinMap, Category.id_comp] at h
    exact h.trans (sliceUnderUncurry_fixed a)
  refine CommSq.HasLift.mk' { l := sliceUnderCurry L hfixed, fac_left := ?_, fac_right := ?_ }
  · apply sliceUnderUncurry_injective p
    rw [sliceUnderUncurry_precomp, sliceUnderUncurry_curry]
    exact hright
  · apply pullback.hom_ext
    · change sliceUnderCurry L hfixed ≫ relativeCosliceMap p q K₀ ≫ r = b ≫ r
      have hr : relativeCosliceMap p q K₀ ≫ r = sliceUnderRestrict p K₀.ι :=
        pullback.lift_fst _ _ _
      rw [hr]
      apply sliceUnderUncurry_injective (K₀.ι ≫ p)
      rw [sliceUnderUncurry_restrict, sliceUnderUncurry_curry]
      exact hleft
    · change sliceUnderCurry L hfixed ≫ relativeCosliceMap p q K₀ ≫ s = b ≫ s
      have hs : relativeCosliceMap p q K₀ ≫ s = sliceUnderPostcomp p q :=
        pullback.lift_snd _ _ _
      rw [hs]
      apply sliceUnderUncurry_injective (p ≫ q)
      rw [sliceUnderUncurry_postcomp, sliceUnderUncurry_curry]
      exact hT.fac_right

/-- 概要：inner fibration の相対 coslice 制限は左ファイブレーション。
方針：左 anodyne な全ての左ホーンに前の補題を適用する。
規約：始域・終域の quasicategory 性は不要。
使われ方：HTT §2.1.2、Kerodon §4.4.2 の相対外側ホーン。 -/
instance relativeCosliceMap_leftFibration {K X Y : SSet.{u}} (p : K ⟶ X) (q : X ⟶ Y)
    [InnerFibration q] (K₀ : K.Subcomplex) : LeftFibration (relativeCosliceMap p q K₀) where
  mem := by
    intro A B f hf
    cases hf with
    | @intro n i hi =>
      exact relativeCosliceMap_hasLiftingProperty p q (horn (n + 1) i) K₀
        (leftAnodyneExtensions_horn i hi)

/-- 概要：左ファイブレーションの引き戻しの第一射影は左ファイブレーション。
方針：左ホーンの rlp の基底変換に対する閉性を使う。
規約：引き戻す左ファイブレーションを第二の射に置く。
使われ方：Kerodon §4.4.2 の相対 coslice の標的。 -/
instance leftFibration_pullback_fst {E B A : SSet.{u}} (p : A ⟶ B) (q : E ⟶ B)
    [LeftFibration q] : LeftFibration (pullback.fst p q) :=
  ⟨leftFibrations.pullback_fst p q (LeftFibration.mem (p := q))⟩

/-- 概要：quasicategory 間の関手の相対 coslice の標的は quasicategory。
方針：始域の部分図式上の coslice への射影の左ファイブレーション性を使う。
規約：射 q の inner fibration 性は不要。
使われ方：Kerodon §4.4.2 の可逆辺を持ち上げる標的。 -/
instance relativeCosliceTarget_quasicategory {K X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (p : K ⟶ X) (q : X ⟶ Y) (K₀ : K.Subcomplex) :
    Quasicategory (relativeCosliceTarget p q K₀) :=
  quasicategory_of_innerFibration (pullback.fst (sliceUnderPostcomp (K₀.ι ≫ p) q)
    (sliceUnderRestrict (p ≫ q) K₀.ι))

end SerrePositivity.InfinityCategories
