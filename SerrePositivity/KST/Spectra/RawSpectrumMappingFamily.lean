module
public import SerrePositivity.KST.Spectra.PostMappingLifts

public import SerrePositivity.KST.Spectra.RawSpectrumMapping
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.RelativePointedHomLifting
public import SerrePositivity.KST.Spectra.PushoutProductMonomorphism

/-!
概要：一般の Kan 列を標的とする整合写像族の、全単射 RLP に沿う相対持ち上げ。
方針：零段は後合成の全単射 RLP、次段は単射な構造射に沿う相対充填を使う。
規約：標的には構造射の単射性も Ω 条件も要求しない。
使われ方：BF 1978 §2、HTT A.3.3、Sp の豊穣 Hom 写像の fibration 性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.Spectra.RawSpectrumMapping

noncomputable section

/-- 概要：段ごとの全単射 RLP に沿う Hom の単射パラメータは各段で整合する族へ持ち上がる。
方針：後合成の初段の持ち上げから始め、構造射の単射性による相対持ち上げを反復する。
規約：単射パラメータ上と底への合成の等式、構造射の整合条件を全て保持する。
使われ方：L9 の実際の Hom 空間の fibration の対角射を構成する。 -/
lemma monoFamily (X : OmegaSpectrum.{u}) {Y Z : KanSequence.{u}}
    (p : KanSequence.Hom Y Z)
    (hp : ∀ n, (MorphismProperty.monomorphisms SSet.{u}).rlp (p.app n).right)
    {T U : SSet.{u}} (j : T ⟶ U) [Mono j]
    (a : T ⟶ space X Y) (b : U ⟶ space X Z)
    (h : a ≫ post X p =
      j ≫ b) :
    ∃ l : ∀ n, U ⟶ (PointedObject.basedHom (X.level n).space (Y.level n).space).right,
      (∀ n, j ≫ l n = a ≫ evaluation X Y n) ∧
      (∀ n, l n ≫ (PointedObject.basedHomMap (X.level n).space (p.app n)).right =
        b ≫ evaluation X Z n) ∧
      (∀ n, l (n + 1) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (X.sigma n) (Y.level (n + 1)).space =
        l n ≫ step X Y n) := by
  let LiftAt (n : ℕ) := {l : U ⟶
      (PointedObject.basedHom (X.level n).space (Y.level n).space).right //
    j ≫ l = a ≫ evaluation X Y n ∧
      l ≫ (PointedObject.basedHomMap (X.level n).space (p.app n)).right =
        b ≫ evaluation X Z n}
  have h0 : Nonempty (LiftAt 0) := by
    have : HasLiftingProperty j
        (PointedObject.basedHomMap (X.level 0).space (p.app 0)).right :=
      PointedMapping.post_rlp_monomorphisms _ _ (hp 0) j inferInstance
    let sq : CommSq (a ≫ evaluation X Y 0) j
        (PointedObject.basedHomMap (X.level 0).space (p.app 0)).right
        (b ≫ evaluation X Z 0) := ⟨by
      rw [Category.assoc, ← post_evaluation X (Y := Y) (Z := Z) p 0,
        ← Category.assoc, h, Category.assoc]⟩
    exact ⟨⟨sq.lift, sq.fac_left, sq.fac_right⟩⟩
  have hn (n : ℕ) (prev : LiftAt n) : ∃ next : LiftAt (n + 1),
      next.val ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (X.sigma n) (Y.level (n + 1)).space =
        prev.val ≫ step X Y n := by
    have hc : j ≫ (prev.val ≫ step X Y n) =
        (a ≫ evaluation X Y (n + 1)) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (X.sigma n) (Y.level (n + 1)).space := by
      rw [← Category.assoc, prev.property.1, Category.assoc,
        ← evaluation_condition, ← Category.assoc]
    have he : (a ≫ evaluation X Y (n + 1)) ≫
        (PointedObject.basedHomMap (X.level (n + 1)).space (p.app (n + 1))).right =
          j ≫ (b ≫ evaluation X Z (n + 1)) := by
      rw [Category.assoc, ← post_evaluation X (Y := Y) (Z := Z) p (n + 1),
        ← Category.assoc, h, Category.assoc]
    have ha : (prev.val ≫ step X Y n) ≫
        (PointedObject.basedHomMap (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space) (p.app (n + 1))).right =
          (b ≫ evaluation X Z (n + 1)) ≫
            _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (X.sigma n) (Z.level (n + 1)).space := by
      change (prev.val ≫ step X Y n) ≫
          (_root_.SerrePositivity.InfinityCategories.HomotopyLimits.pointedMappingFunctor (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space)).map (p.app (n + 1)) = _
      rw [Category.assoc, step_post X (Y := Y) (Z := Z) p n,
        ← Category.assoc]
      change (prev.val ≫ (PointedObject.basedHomMap (X.level n).space (p.app n)).right) ≫
        step X Z n = _
      rw [prev.property.2, Category.assoc, ← evaluation_condition,
        ← Category.assoc]
    let pp := Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet.{u}) (X.sigma n).right j
    have hpp : HasLiftingProperty pp.ι (p.app (n + 1)).right :=
      hp (n + 1) pp.ι (PushoutProductMonomorphism.mono pp)
    obtain ⟨l, hl, hp, hb⟩ := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.relativePointedHom_lift (X.sigma n) (p.app (n + 1)) j hpp
      (a ≫ evaluation X Y (n + 1)) (prev.val ≫ step X Y n)
      (b ≫ evaluation X Z (n + 1)) hc he ha
    exact ⟨⟨l, hl, hb⟩, hp⟩
  let stage : ∀ n, LiftAt n := Nat.rec (Classical.choice h0) (fun n prev ↦ (hn n prev).choose)
  refine ⟨fun n ↦ (stage n).val, fun n ↦ (stage n).property.1,
    fun n ↦ (stage n).property.2, ?_⟩
  intro n
  exact (hn n (stage n)).choose_spec

end
end SerrePositivity.KST.Spectra.RawSpectrumMapping
