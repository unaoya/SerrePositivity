module
public import SerrePositivity.KST.Spectra.PostMappingFibration

public import SerrePositivity.KST.Spectra.RawSpectrumMappingFamily

/-!
概要：段ごとに Kan fibration である列の射に対し、BF 写像空間の anodyne 族を持ち上げる。
方針：基点・構造射と anodyne パラメータの pushout-product を帰納的に充填する。
規約：単射への全 RLP を要求しない。使われ方：coherent な右辺比較の厳密化。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.LocalizingInvariants.FiberMapping
open RawSpectrumMapping

lemma anodyneFamily (X : OmegaSpectrum.{u}) {Y Z : KanSequence.{u}}
    (p : KanSequence.Hom Y Z) (hp : ∀ n, Fibration (p.app n).right)
    {T U : SSet.{u}} (j : T ⟶ U) (hj : anodyneExtensions j)
    (a : T ⟶ space X Y) (b : U ⟶ space X Z) (h : a ≫ post X p = j ≫ b) :
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
    let pp := Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet.{u})
      (X.level 0).space.hom j
    let : Mono (X.level 0).space.hom := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.basepoint_mono _
    have hpp : HasLiftingProperty pp.ι (p.app 0).right :=
      (anodyneExtensions_pushoutObjObjι pp hj) _ ((SSet.modelCategoryQuillen.fibration_iff _).1 (hp 0))
    have : HasLiftingProperty j
        (PointedObject.basedHomMap (X.level 0).space (p.app 0)).right :=
      PointedMapping.post_hasLiftingProperty _ _ j hpp
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
      (anodyneExtensions_pushoutObjObjι pp hj) _ ((SSet.modelCategoryQuillen.fibration_iff _).1 (hp (n + 1)))
    obtain ⟨l, hl, hp, hb⟩ := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.relativePointedHom_lift (X.sigma n) (p.app (n + 1)) j hpp
      (a ≫ evaluation X Y (n + 1)) (prev.val ≫ step X Y n)
      (b ≫ evaluation X Z (n + 1)) hc he ha
    exact ⟨⟨l, hl, hb⟩, hp⟩
  let stage : ∀ n, LiftAt n := Nat.rec (Classical.choice h0) (fun n prev ↦ (hn n prev).choose)
  refine ⟨fun n ↦ (stage n).val, fun n ↦ (stage n).property.1,
    fun n ↦ (stage n).property.2, ?_⟩
  intro n
  exact (hn n (stage n)).choose_spec


end SerrePositivity.KST.LocalizingInvariants.FiberMapping
