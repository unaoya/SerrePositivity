module

public import SerrePositivity.InfinityCategories.HomotopyLimits.SpectrumMappingDiagram
public import SerrePositivity.KST.Spectra.PostMappingFibration

/-!
概要：点つき Hom の源の制限と標的の fibration を同時に保つホーン充填。
方針：単射とホーンの pushout-product を uncurry した族に適用する。
規約：源とパラメータに Kan 性は要求しない。
使われ方：BF 1978 §2、HTT A.3.3、HTT 4.2.4.1 のスペクトルの Hom 写像の fibration 性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory
open SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open SerrePositivity.KST.Spectra
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section

/-- 概要：pushout-product に対する持ち上げ性は二つの部分を固定する積上の充填を与える。
方針：二つの族を pushout に貼り合わせて対角射を取り、両脚の合成を計算する。
規約：持ち上げ性を一つの明示した pushout-product について要求する。
使われ方：点つき Hom の相対ホーン充填の uncurry 側の構成。 -/
lemma relativeTensorLift {A X E B T U : SSet.{u}} (p : E ⟶ B) (i : A ⟶ X) (j : T ⟶ U)
    (h : HasLiftingProperty (Functor.PushoutObjObj.ofHasPushout
      (curriedTensor SSet.{u}) i j).ι p)
    (earlier : X ⊗ T ⟶ E) (prescribed : A ⊗ U ⟶ E) (base : X ⊗ U ⟶ B)
    (hc : i ▷ T ≫ earlier = A ◁ j ≫ prescribed)
    (he : earlier ≫ p = X ◁ j ≫ base) (ha : prescribed ≫ p = i ▷ U ≫ base) :
    ∃ l : X ⊗ U ⟶ E, X ◁ j ≫ l = earlier ∧ i ▷ U ≫ l = prescribed ∧ l ≫ p = base := by
  let pp := Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet.{u}) i j
  have : HasLiftingProperty pp.ι p := h
  let a := pp.isPushout.desc earlier prescribed hc
  have hw : a ≫ p = pp.ι ≫ base := by
    apply pp.isPushout.hom_ext
    · dsimp only [a]
      rw [← Category.assoc, pp.isPushout.inl_desc, he, ← Category.assoc, pp.inl_ι]
      rfl
    · dsimp only [a]
      rw [← Category.assoc, pp.isPushout.inr_desc, ha, ← Category.assoc, pp.inr_ι]
      rfl
  let sq : CommSq a pp.ι p base := ⟨hw⟩
  refine ⟨sq.lift, ?_, ?_, sq.fac_right⟩
  · rw [show X ◁ j = pp.inl ≫ pp.ι from pp.inl_ι.symm, Category.assoc, sq.fac_left]
    exact pp.isPushout.inl_desc _ _ _
  · rw [show i ▷ U = pp.inr ≫ pp.ι from pp.inr_ι.symm, Category.assoc, sq.fac_left]
    exact pp.isPushout.inr_desc _ _ _

/-- 概要：単射に沿う制限と Kan fibration への後合成を同時に保って点つき Hom のホーンを充填する。
方針：uncurry した族を pushout-product に沿って持ち上げ、源の基点条件を指定部分から戻す。
規約：源の Kan 性・標的の Kan 性・Ω 条件を仮定しない。
使われ方：スペクトルの各段の Hom の相対充填を帰納的に構成する。 -/
lemma relativePointedHom_hornLift {A X E B : PointedSimplicialSet.{u}}
    (i : A ⟶ X) [Mono i.right] (p : E ⟶ B) [Fibration p.right]
    {T U : SSet.{u}} (j : T ⟶ U) (hj : J j)
    (a : T ⟶ (PointedObject.basedHom X E).right)
    (b : U ⟶ (PointedObject.basedHom A E).right)
    (c : U ⟶ (PointedObject.basedHom X B).right)
    (hc : j ≫ b = a ≫ PointedMapping.pre i E)
    (he : a ≫ (PointedObject.basedHomMap X p).right = j ≫ c)
    (ha : b ≫ (PointedObject.basedHomMap A p).right = c ≫ PointedMapping.pre i B) :
    ∃ l : U ⟶ (PointedObject.basedHom X E).right,
      j ≫ l = a ∧ l ≫ PointedMapping.pre i E = b ∧
        l ≫ (PointedObject.basedHomMap X p).right = c := by
  let earlier := MonoidalClosed.uncurry (a ≫ PointedObject.basedHomι X E)
  let prescribed := MonoidalClosed.uncurry (b ≫ PointedObject.basedHomι A E)
  let base := MonoidalClosed.uncurry (c ≫ PointedObject.basedHomι X B)
  have hcompat : i.right ▷ T ≫ earlier = A.right ◁ j ≫ prescribed := by
    have h := congrArg (fun k : T ⟶ (PointedObject.basedHom A E).right ↦
      MonoidalClosed.uncurry (k ≫ PointedObject.basedHomι A E)) hc
    simp only [Category.assoc, PointedMapping.pre_ι, MonoidalClosed.uncurry_natural_left] at h
    exact h.symm
  have hearlier : earlier ≫ p.right = X.right ◁ j ≫ base := by
    dsimp only [earlier, base]
    rw [← MonoidalClosed.uncurry_natural_right, Category.assoc,
      ← PointedObject.basedHomMap_ι, ← Category.assoc, he,
      MonoidalClosed.uncurry_natural_left]
    rfl
  have hprescribed : prescribed ≫ p.right = i.right ▷ U ≫ base := by
    dsimp only [prescribed, base]
    rw [← MonoidalClosed.uncurry_natural_right, Category.assoc,
      ← PointedObject.basedHomMap_ι, ← Category.assoc, ha, Category.assoc,
      PointedMapping.pre_ι, ← Category.assoc, MonoidalClosed.uncurry_pre_app]
  let pp := Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet.{u}) i.right j
  have hj' : anodyneExtensions j := by
    rw [anodyneExtensions_eq_llp_rlp]
    exact MorphismProperty.le_llp_rlp J _ hj
  have hpp : HasLiftingProperty pp.ι p.right :=
    (anodyneExtensions_pushoutObjObjι pp hj') p.right
      ((SSet.modelCategoryQuillen.fibration_iff _).mp inferInstance)
  obtain ⟨l, hl, hi, hp⟩ := relativeTensorLift p.right i.right j hpp
    earlier prescribed base hcompat hearlier hprescribed
  have hfixed : X.hom ▷ U ≫ l = toUnit (𝟙_ SSet.{u} ⊗ U) ≫ E.hom := by
    rw [← Under.w i, comp_whiskerRight, Category.assoc, hi]
    exact PointedMapping.uncurry_basepoint A E b
  refine ⟨PointedMapping.paramCurry X E l hfixed, ?_, ?_, ?_⟩
  · apply (cancel_mono (PointedObject.basedHomι X E)).mp
    rw [Category.assoc, PointedMapping.paramCurry_ι, ← MonoidalClosed.curry_natural_left,
      hl, MonoidalClosed.curry_uncurry]
  · apply (cancel_mono (PointedObject.basedHomι A E)).mp
    rw [Category.assoc, PointedMapping.pre_ι, ← Category.assoc,
      PointedMapping.paramCurry_ι, MonoidalClosed.curry_pre_app, hi,
      MonoidalClosed.curry_uncurry]
  · apply (cancel_mono (PointedObject.basedHomι X B)).mp
    rw [Category.assoc, PointedObject.basedHomMap_ι, ← Category.assoc,
      PointedMapping.paramCurry_ι, ← MonoidalClosed.curry_natural_right, hp,
      MonoidalClosed.curry_uncurry]

end
end SerrePositivity.InfinityCategories.HomotopyLimits
