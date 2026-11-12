module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word
public import SerrePositivity.EInfinity.Hammock.WeakPushoutGluing
public import Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
# 二つの向きで添字づけられた元の余積の弱同値

概要：向きの二要素集合と同値な添字の元の余積は成分ごとの弱同値を保つ。
方針：元の二つの余積包含を二項余積の余錐とし、初期対象からの pushout を使う。
規約：結論は元の Sigma.map。元の対象に Kan 性やモデル構造を課さない。
使われ方：長さ段階の最大交互語と境界の余積の比較。
-/

@[expose] public section
universe w
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock
open CategoryTheory CategoryTheory.Limits
open SerrePositivity.InfinityCategories

variable {I : Type} (e : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction ≃ I) (A : I → SSet.{w})

def twoIndexBinaryCofan : BinaryCofan (A (e .forward)) (A (e .backward)) :=
  BinaryCofan.mk (Sigma.ι A (e .forward)) (Sigma.ι A (e .backward))

def twoIndexBinaryCofan_isColimit : IsColimit (twoIndexBinaryCofan e A) := by
  refine BinaryCofan.isColimitMk (fun s =>
    (Sigma.reindex e A).inv ≫ Sigma.desc (fun d => match d with
      | .forward => s.inl
      | .backward => s.inr)) ?_ ?_ ?_
  · intro s
    simp [← Category.assoc]
  · intro s
    simp [← Category.assoc]
  · intro s m hl hr
    apply Sigma.hom_ext
    intro i
    obtain ⟨d, rfl⟩ := e.surjective i
    cases d
    · simpa [twoIndexBinaryCofan, ← Category.assoc] using hl
    · simpa [twoIndexBinaryCofan, ← Category.assoc] using hr

include e in
lemma weakTwoIndexCoproduct {B : I → SSet.{w}} (f : ∀ i, A i ⟶ B i)
    (hf : ∀ i, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (f i)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (Limits.Sigma.map f) := by
  have hA := IsPushout.of_is_coproduct (twoIndexBinaryCofan_isColimit e A)
    (initialIsInitial : IsInitial (⊥_ SSet.{w}))
  have hB := IsPushout.of_is_coproduct (twoIndexBinaryCofan_isColimit e B)
    (initialIsInitial : IsInitial (⊥_ SSet.{w}))
  exact weakPushout_gluing hA hB (𝟙 _) (f (e .forward)) (f (e .backward))
    (Limits.Sigma.map f)
    (initialIsInitial.hom_ext _ _) (initialIsInitial.hom_ext _ _)
    (Sigma.ι_map _ _) (Sigma.ι_map _ _)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.isWeakHomotopyEquivalence_id _) (hf _) (hf _)

end SerrePositivity.EInfinity.Hammock
