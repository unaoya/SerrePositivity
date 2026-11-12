module

public import SerrePositivity.KST.Spectra.PostMappingFibration
public import SerrePositivity.KST.Spectra.PathNaturality

/-!
概要：点つき Hom の源の制限と標的の射を同時に指定する corner。
方針：可換正方形の pullback を取り、パラメータ付きの持ち上げを積の族へ移す。
規約：通常の単体集合の pullback。ModelCategory の仮定は使わない。
使われ方：Goerss–Jardine I §7–8。path と fiber の連結射を同時に比較する。
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

variable {A X E B : PointedSimplicialSet.{u}} (i : A ⟶ X) (p : E ⟶ B)

/-- 概要：源上の指定族と射影先の族が一致する条件を表す pullback。
方針：源の制限と標的の後合成の二射を使う。
規約：二つの射影はそれぞれ X から B、A から E への写像空間。
使われ方：Goerss–Jardine I §7。相対写像空間の持ち上げ先。 -/
abbrev cornerTarget : SSet.{u} := pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre i B) (PointedObject.basedHomMap A p).right

/-- 概要：一つの写像族を、底への族と指定部分上の族へ制限する射。
方針：前合成と後合成の可換性から pullback へ持ち上げる。
規約：pointed Hom の基礎単体集合の射。
使われ方：Goerss–Jardine I §7–8。二種類の境界を同時に指定する。 -/
def corner : (PointedObject.basedHom X E).right ⟶ cornerTarget i p :=
  pullback.lift (PointedObject.basedHomMap X p).right (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre i E)
    (congrArg Under.Hom.right (prePointed_post i p)).symm

@[reassoc (attr := simp)]
lemma corner_fst : corner i p ≫ pullback.fst _ _ = (PointedObject.basedHomMap X p).right :=
  pullback.lift_fst ..

@[reassoc (attr := simp)]
lemma corner_snd : corner i p ≫ pullback.snd _ _ = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre i E := pullback.lift_snd ..

/-- 概要：corner のパラメータの持ち上げ性を積の相対持ち上げ性から得る。
方針：pullback の二射影を uncurry し、指定部分・既存部分・底を同時に保つ。
規約：必要な pushout-product の持ち上げ性だけを仮定する。
使われ方：Goerss–Jardine I §7–8。path の相対 fibration の構成。 -/
theorem corner_hasLiftingProperty {T U : SSet.{u}} (j : T ⟶ U)
    (h : HasLiftingProperty
      (Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet.{u}) i.right j).ι p.right) :
    HasLiftingProperty j (corner i p) := by
  constructor
  intro a b sq
  let earlier := uncurry (a ≫ PointedObject.basedHomι X E)
  let prescribed := uncurry (b ≫ pullback.snd _ _ ≫ PointedObject.basedHomι A E)
  let base := uncurry (b ≫ pullback.fst _ _ ≫ PointedObject.basedHomι X B)
  have hs : a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre i E = j ≫ b ≫ pullback.snd _ _ := by
    have hs := congrArg (fun f ↦ f ≫ pullback.snd _ _) sq.w
    simpa only [Category.assoc, corner_snd] using hs
  have hf : a ≫ (PointedObject.basedHomMap X p).right = j ≫ b ≫ pullback.fst _ _ := by
    have hf := congrArg (fun f ↦ f ≫ pullback.fst _ _) sq.w
    simpa only [Category.assoc, corner_fst] using hf
  have hc : i.right ▷ T ≫ earlier = A.right ◁ j ≫ prescribed := by
    dsimp only [earlier, prescribed]
    rw [← uncurry_natural_left, ← uncurry_pre_app, Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre_ι,
      ← Category.assoc, hs]
    rfl
  have he : earlier ≫ p.right = X.right ◁ j ≫ base := by
    dsimp only [earlier, base]
    rw [← uncurry_natural_right, Category.assoc, ← PointedObject.basedHomMap_ι,
      ← Category.assoc, hf, uncurry_natural_left]
    rfl
  have ha : prescribed ≫ p.right = i.right ▷ U ≫ base := by
    dsimp only [prescribed, base]
    rw [← uncurry_natural_right]
    simp only [Category.assoc]
    rw [← PointedObject.basedHomMap_ι, ← pullback.condition_assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre_ι,
      ← Category.assoc, ← Category.assoc, uncurry_pre_app]
    rfl
  obtain ⟨f, hearlier, hprescribed, hbase⟩ := relative_product_lift p.right i.right j h
    earlier prescribed base hc he ha
  have hfixed : X.hom ▷ U ≫ f = toUnit (𝟙_ SSet.{u} ⊗ U) ≫ E.hom := by
    rw [← Under.w i, comp_whiskerRight_assoc, hprescribed]
    exact _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.uncurry_basepoint A E (b ≫ pullback.snd _ _)
  let l := _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.paramCurry X E f hfixed
  refine ⟨⟨{ l := l, fac_left := ?_, fac_right := ?_ }⟩⟩
  · apply (cancel_mono (PointedObject.basedHomι X E)).mp
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.paramCurry_ι, ← curry_natural_left, hearlier, curry_uncurry]
  · apply pullback.hom_ext
    · apply (cancel_mono (PointedObject.basedHomι X B)).mp
      simp only [Category.assoc, corner_fst_assoc]
      rw [PointedObject.basedHomMap_ι,
        ← Category.assoc, _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.paramCurry_ι, ← curry_natural_right, hbase, curry_uncurry]
    · apply (cancel_mono (PointedObject.basedHomι A E)).mp
      simp only [Category.assoc, corner_snd_assoc]
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre_ι,
        ← Category.assoc, _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.paramCurry_ι, curry_pre_app, hprescribed, curry_uncurry]

/-- 概要：源の単射と標的の Kan fibration から corner の Kan fibration を得る。
方針：ホーンと単射の pushout-product の anodyne 性を相対族の持ち上げに適用する。
規約：安定モデル構造や Kan–Quillen モデル構造を要求しない。
使われ方：Goerss–Jardine I §7–8。二つの連結射の比較用の共通持ち上げ。 -/
instance corner_fibration [Mono i.right] [Fibration p.right] : Fibration (corner i p) := by
  rw [fibration_iff]
  intro T U j hj
  let pp := Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet.{u}) i.right j
  have hj' : anodyneExtensions j := by
    rw [anodyneExtensions_eq_llp_rlp]
    exact MorphismProperty.le_llp_rlp J _ hj
  have h := (anodyneExtensions_pushoutObjObjι pp hj') p.right
    ((fibration_iff _).1 inferInstance)
  exact corner_hasLiftingProperty i p j h

end
end SerrePositivity.KST.Spectra.PointedMapping
