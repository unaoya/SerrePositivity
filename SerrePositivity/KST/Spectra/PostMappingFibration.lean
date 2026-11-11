module

public import SerrePositivity.KST.Spectra.PostMappingLifts

/-!
概要：点つき Hom の後合成は Kan fibration を保存する。
方針：源の基点包含とホーン包含の pushout product の anodyne 性を使う。
規約：弱同値クラスや HT-KQ は用いない。
使われ方：Kerodon §3.1.3（Tag 00TJ）、Goerss–Jardine I §7、BF 1978 §2。loop による fiber 列の保存。
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory
open SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen

namespace SerrePositivity.KST.Spectra.PointedMapping

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：指定部分と既存パラメータ上の族を、pushout product の RLP で同時に延長する。
方針：二つの族を pushout に貼り、指定された持ち上げ性で解く。
規約：この補題では必要な一つの持ち上げ性を明示する。
使われ方：Kerodon §3.1.3（Tag 00TJ）、Goerss–Jardine I §7。点つき Hom のホーン充填。 -/
theorem relative_product_lift {E B A X T U : SSet.{u}} (p : E ⟶ B)
    (i : A ⟶ X) (j : T ⟶ U)
    (h : HasLiftingProperty (Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet.{u}) i j).ι p)
    (earlier : X ⊗ T ⟶ E) (prescribed : A ⊗ U ⟶ E) (base : X ⊗ U ⟶ B)
    (hc : i ▷ T ≫ earlier = A ◁ j ≫ prescribed)
    (he : earlier ≫ p = X ◁ j ≫ base) (ha : prescribed ≫ p = i ▷ U ≫ base) :
    ∃ f : X ⊗ U ⟶ E, X ◁ j ≫ f = earlier ∧ i ▷ U ≫ f = prescribed ∧ f ≫ p = base := by
  let pp := Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet.{u}) i j
  let : HasLiftingProperty pp.ι p := h
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

/-- 概要：基点とパラメータの pushout product に対する RLP から後合成の RLP を得る。
方針：uncurry した族を基点上の定数族と同時に持ち上げ、等化子へ curry する。
規約：パラメータの射は任意。
使われ方：Kerodon §3.1.3（Tag 00TJ）、Goerss–Jardine I §7。loop の fibration 保存。 -/
theorem post_hasLiftingProperty (A : PointedSimplicialSet.{u})
    {E B : PointedSimplicialSet.{u}} (p : E ⟶ B) {T U : SSet.{u}} (j : T ⟶ U)
    (h : HasLiftingProperty
      (Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet.{u}) A.hom j).ι p.right) :
    HasLiftingProperty j (PointedObject.basedHomMap A p).right := by
  constructor
  intro a b sq
  let earlier := MonoidalClosed.uncurry (a ≫ PointedObject.basedHomι A E)
  let prescribed := toUnit (𝟙_ SSet.{u} ⊗ U) ≫ E.hom
  let base := MonoidalClosed.uncurry (b ≫ PointedObject.basedHomι A B)
  have hc : A.hom ▷ T ≫ earlier = 𝟙_ SSet.{u} ◁ j ≫ prescribed := by
    rw [_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.uncurry_basepoint]
    simp only [prescribed, comp_toUnit_assoc]
  have he : earlier ≫ p.right = A.right ◁ j ≫ base := by
    dsimp only [earlier, base]
    rw [← MonoidalClosed.uncurry_natural_right, Category.assoc,
      ← PointedObject.basedHomMap_ι, ← Category.assoc, sq.w,
      MonoidalClosed.uncurry_natural_left]
    rfl
  have ha : prescribed ≫ p.right = A.hom ▷ U ≫ base := by
    rw [_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.uncurry_basepoint]
    simp only [prescribed, Category.assoc, Under.w]
  obtain ⟨f, hf, hfixed, hbase⟩ := relative_product_lift p.right A.hom j h
    earlier prescribed base hc he ha
  let l := _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.paramCurry A E f hfixed
  refine ⟨⟨{ l := l, fac_left := ?_, fac_right := ?_ }⟩⟩
  · apply (cancel_mono (PointedObject.basedHomι A E)).mp
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.paramCurry_ι, ← MonoidalClosed.curry_natural_left,
      hf, MonoidalClosed.curry_uncurry]
  · apply (cancel_mono (PointedObject.basedHomι A B)).mp
    rw [Category.assoc, PointedObject.basedHomMap_ι, ← Category.assoc,
      _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.paramCurry_ι, ← MonoidalClosed.curry_natural_right, hbase,
      MonoidalClosed.curry_uncurry]

/-- 概要：点つき内部 Hom の後合成は Kan fibration を保つ。
方針：基点包含は単射、ホーンは anodyne なのでその pushout product を充填できる。
規約：源の Kan 性は不要。
使われ方：Kerodon §3.1.3（Tag 00TJ）、Goerss–Jardine I §7、BF 1978 §2。loop の fibration 保存。 -/
instance post_fibration (A : PointedSimplicialSet.{u}) {E B : PointedSimplicialSet.{u}}
    (p : E ⟶ B) [Fibration p.right] : Fibration (PointedObject.basedHomMap A p).right := by
  rw [fibration_iff]
  intro T U j hj
  let : Mono A.hom := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.basepoint_mono A
  let pp := Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet.{u}) A.hom j
  have hj' : anodyneExtensions j := by
    rw [anodyneExtensions_eq_llp_rlp]
    exact MorphismProperty.le_llp_rlp J _ hj
  have h := (anodyneExtensions_pushoutObjObjι pp hj') p.right
    ((fibration_iff _).1 inferInstance)
  exact post_hasLiftingProperty A p j h

end

end SerrePositivity.KST.Spectra.PointedMapping
