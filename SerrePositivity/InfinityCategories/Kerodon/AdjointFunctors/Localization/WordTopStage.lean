module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordLength
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAlternating
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordMergeCone
public import Mathlib.CategoryTheory.Limits.Final

/-!
# 最大長の語を交互方向語だけに制限した添字圏

概要：前段階の全語と最大長の交互方向語からなる全部分圏を構成する。
方針：省いた最大長の語からの射は非単射で、二つの基本合成は短い語で結べる。
規約：元の語と元の写像を保持する。
使われ方：長さ段階の余極限を貼り合わせで表示する工程。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

def topStageProperty (n : ℕ) : ObjectProperty (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LengthBounded n) :=
  fun a => a.obj.length < n ∨ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.IsAlternating a.obj

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (topStageProperty)


abbrev TopStage (n : ℕ) := (topStageProperty n).FullSubcategory

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (TopStage)


def topStageInclusion (n : ℕ) : TopStage n ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LengthBounded n := (topStageProperty n).ι

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (topStageInclusion)


lemma not_injective_of_not_top {n : ℕ} (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LengthBounded n) (ha : ¬ topStageProperty n a)
    (b : TopStage n) (f : a.obj ⟶ b.obj.obj) : ¬ Function.Injective f.orderHom := by
  intro hf
  have hab : a.obj.length ≤ b.obj.obj.length := by
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective _ hf
  rcases b.property with hb | hb
  · exact ha (Or.inl (hab.trans_lt hb))
  · have hn : n ≤ a.obj.length := Nat.le_of_not_gt (fun h => ha (Or.inl h))
    have hba : b.obj.obj.length ≤ a.obj.length := b.obj.property.trans hn
    have hs : Function.Surjective f.orderHom := by
      by_contra h
      have hc := Fintype.card_lt_of_injective_not_surjective f.orderHom hf h
      simp only [Fintype.card_fin] at hc
      exact Nat.not_lt_of_ge hba hc
    obtain ⟨h, _⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.embedding_eq_of_range f (𝟙 b.obj.obj) hf Function.injective_id
      (by rw [Set.range_eq_univ.mpr hs]; exact Set.range_id.symm)
    apply ha
    right
    rw [h]
    exact hb

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (not_injective_of_not_top)


def topMergeObject (n : ℕ) {k : ℕ} (d : Fin (k + 2) → _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction)
    (hn : k + 2 ≤ n) (p : Fin (k + 1)) : TopStage n :=
  ⟨⟨_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.mergeTarget d p, (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) hn).le⟩,
    Or.inl (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) hn)⟩

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (topMergeObject)


def topMergeArrow (n : ℕ) {k : ℕ} (d : Fin (k + 2) → _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction)
    (hn : k + 2 ≤ n) (p : Fin (k + 1)) (hp : d p.castSucc = d p.succ) :
    StructuredArrow (⟨⟨k + 2, d⟩, hn⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LengthBounded n) (topStageInclusion n) :=
  StructuredArrow.mk (Y := topMergeObject n d hn p) (ObjectProperty.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.mergeMap d p hp))

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (topMergeArrow)


lemma topMergeArrow_zigzag (n : ℕ) {k : ℕ} (d : Fin (k + 2) → _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction)
    (hn : k + 2 ≤ n) (p q : Fin (k + 1))
    (hp : d p.castSucc = d p.succ) (hq : d q.castSucc = d q.succ) :
    Zigzag (topMergeArrow n d hn p hp) (topMergeArrow n d hn q hq) := by
  obtain ⟨b, hb, l, r, he⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.merge_cone d p q hp hq
  let B : TopStage n := ⟨⟨b, (hb.trans_le hn).le⟩, Or.inl (hb.trans_le hn)⟩
  let t : StructuredArrow (⟨⟨k + 2, d⟩, hn⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LengthBounded n) (topStageInclusion n) :=
    StructuredArrow.mk (Y := B) (ObjectProperty.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.mergeMap d p hp ≫ l))
  have hl : topMergeArrow n d hn p hp ⟶ t :=
    StructuredArrow.homMk (ObjectProperty.homMk (ObjectProperty.homMk l)) rfl
  have hr : topMergeArrow n d hn q hq ⟶ t :=
    StructuredArrow.homMk (ObjectProperty.homMk (ObjectProperty.homMk r)) (by
      apply ObjectProperty.hom_ext
      exact he.symm)
  exact Zigzag.of_hom_inv hl hr

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (topMergeArrow_zigzag)


end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
