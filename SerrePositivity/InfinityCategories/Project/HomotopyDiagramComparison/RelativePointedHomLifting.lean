module

public import SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.PointedMappingParameters
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping
public import SerrePositivity.Spectra.Pointed.InternalHom
public import SerrePositivity.Spectra.PointedSimplicialSet.Basic

/-!
概要：点つき Hom の源の制限と標的への合成を同時に保つ相対充填。
方針：pushout-product の持ち上げ性を uncurry した族へ適用し、ホーンと anodyne な源に使う。
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
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
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

/-- 概要：一つの pushout-product の持ち上げ性から点つき Hom の相対充填を構成する。
方針：uncurry した族を持ち上げ、指定部分に含まれる源の基点の条件を戻す。
規約：単射性や fibration 性を先に要求せず、必要な持ち上げ性を明示する。
使われ方：ホーンの充填と anodyne な源に沿う全単射 RLP の共通の構成。 -/
lemma relativePointedHom_lift {A X E B : PointedSimplicialSet.{u}}
    (i : A ⟶ X) (p : E ⟶ B)
    {T U : SSet.{u}} (j : T ⟶ U)
    (hpp : HasLiftingProperty (Functor.PushoutObjObj.ofHasPushout
      (curriedTensor SSet.{u}) i.right j).ι p.right)
    (a : T ⟶ (PointedObject.basedHom X E).right)
    (b : U ⟶ (PointedObject.basedHom A E).right)
    (c : U ⟶ (PointedObject.basedHom X B).right)
    (hc : j ≫ b = a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre i E)
    (he : a ≫ (PointedObject.basedHomMap X p).right = j ≫ c)
    (ha : b ≫ (PointedObject.basedHomMap A p).right = c ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre i B) :
    ∃ l : U ⟶ (PointedObject.basedHom X E).right,
      j ≫ l = a ∧ l ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre i E = b ∧
        l ≫ (PointedObject.basedHomMap X p).right = c := by
  let earlier := MonoidalClosed.uncurry (a ≫ PointedObject.basedHomι X E)
  let prescribed := MonoidalClosed.uncurry (b ≫ PointedObject.basedHomι A E)
  let base := MonoidalClosed.uncurry (c ≫ PointedObject.basedHomι X B)
  have hcompat : i.right ▷ T ≫ earlier = A.right ◁ j ≫ prescribed := by
    have h := congrArg (fun k : T ⟶ (PointedObject.basedHom A E).right ↦
      MonoidalClosed.uncurry (k ≫ PointedObject.basedHomι A E)) hc
    simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre_ι, MonoidalClosed.uncurry_natural_left] at h
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
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre_ι, ← Category.assoc, MonoidalClosed.uncurry_pre_app]
  obtain ⟨l, hl, hi, hp⟩ := relativeTensorLift p.right i.right j hpp
    earlier prescribed base hcompat hearlier hprescribed
  have hfixed : X.hom ▷ U ≫ l = toUnit (𝟙_ SSet.{u} ⊗ U) ≫ E.hom := by
    rw [← Under.w i, comp_whiskerRight, Category.assoc, hi]
    exact _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.uncurry_basepoint A E b
  refine ⟨_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.paramCurry X E l hfixed, ?_, ?_, ?_⟩
  · apply (cancel_mono (PointedObject.basedHomι X E)).mp
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.paramCurry_ι, ← MonoidalClosed.curry_natural_left,
      hl, MonoidalClosed.curry_uncurry]
  · apply (cancel_mono (PointedObject.basedHomι A E)).mp
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre_ι, ← Category.assoc,
      _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.paramCurry_ι, MonoidalClosed.curry_pre_app, hi,
      MonoidalClosed.curry_uncurry]
  · apply (cancel_mono (PointedObject.basedHomι X B)).mp
    rw [Category.assoc, PointedObject.basedHomMap_ι, ← Category.assoc,
      _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.paramCurry_ι, ← MonoidalClosed.curry_natural_right, hp,
      MonoidalClosed.curry_uncurry]

/-- 概要：単射に沿う制限と Kan fibration への後合成を同時に保ってホーンを充填する。
方針：単射とホーンの pushout-product の anodyne 性を一般の相対充填へ渡す。
規約：源の Kan 性・標的の Kan 性・Ω 条件は不要。
使われ方：スペクトルの各段の Hom の相対充填。 -/
lemma relativePointedHom_hornLift {A X E B : PointedSimplicialSet.{u}}
    (i : A ⟶ X) [Mono i.right] (p : E ⟶ B) [Fibration p.right]
    {T U : SSet.{u}} (j : T ⟶ U) (hj : J j)
    (a : T ⟶ (PointedObject.basedHom X E).right)
    (b : U ⟶ (PointedObject.basedHom A E).right)
    (c : U ⟶ (PointedObject.basedHom X B).right)
    (hc : j ≫ b = a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre i E)
    (he : a ≫ (PointedObject.basedHomMap X p).right = j ≫ c)
    (ha : b ≫ (PointedObject.basedHomMap A p).right = c ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre i B) :
    ∃ l : U ⟶ (PointedObject.basedHom X E).right,
      j ≫ l = a ∧ l ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre i E = b ∧
        l ≫ (PointedObject.basedHomMap X p).right = c := by
  let pp := Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet.{u}) i.right j
  have hj' : anodyneExtensions j := by
    rw [anodyneExtensions_eq_llp_rlp]
    exact MorphismProperty.le_llp_rlp J _ hj
  have hpp : HasLiftingProperty pp.ι p.right :=
    (anodyneExtensions_pushoutObjObjι pp hj') p.right
      ((SSet.modelCategoryQuillen.fibration_iff _).mp inferInstance)
  exact relativePointedHom_lift i p j hpp a b c hc he ha

/-- 概要：anodyne な源の制限と Kan fibration への後合成は全ての単射パラメータで相対充填できる。
方針：anodyne な源と単射の pushout-product を一般の相対充填へ渡す。
規約：源の Kan 性を仮定せず、以前の族・指定部分・底への合成を保つ。
使われ方：塔の mapping path の相対比較の全単射 RLP。 -/
lemma relativePointedHom_anodyneLift {A X E B : PointedSimplicialSet.{u}}
    (i : A ⟶ X) (hi : anodyneExtensions i.right) (p : E ⟶ B) [Fibration p.right]
    {T U : SSet.{u}} (j : T ⟶ U) [Mono j]
    (a : T ⟶ (PointedObject.basedHom X E).right)
    (b : U ⟶ (PointedObject.basedHom A E).right)
    (c : U ⟶ (PointedObject.basedHom X B).right)
    (hc : j ≫ b = a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre i E)
    (he : a ≫ (PointedObject.basedHomMap X p).right = j ≫ c)
    (ha : b ≫ (PointedObject.basedHomMap A p).right = c ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre i B) :
    ∃ l : U ⟶ (PointedObject.basedHom X E).right,
      j ≫ l = a ∧ l ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre i E = b ∧
        l ≫ (PointedObject.basedHomMap X p).right = c := by
  let pp := Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet.{u}) i.right j
  have hpp : HasLiftingProperty pp.ι p.right :=
    (anodyneExtensions_pushoutObjObjι' pp hi) p.right
      ((SSet.modelCategoryQuillen.fibration_iff _).mp inferInstance)
  exact relativePointedHom_lift i p j hpp a b c hc he ha

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
