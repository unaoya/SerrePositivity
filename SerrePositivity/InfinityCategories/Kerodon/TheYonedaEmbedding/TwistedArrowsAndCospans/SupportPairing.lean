module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.SupportPivot

/-!
概要：twisted arrow の延長領域外の頂点集合で、内部の挿入点の挿入・削除を整合させる。
方針：指定番号以外の全ての対を保ち、挿入点の分岐条件も保つことを示す。
規約：単体的 pairing の正則性と anodyne 性は後続の工程。
使われ方：twisted arrow 射影を left fibration とする inner horn の接合。

対応節は Kerodon 8.1（Tag 03JB）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans

/-- 選んだ点の挿入は、それを選ぶ左右の分岐条件を変えない。 -/
lemma twistedArrowHasUpperLeft_insert_pivot_iff {n : ℕ} (i : Fin (n + 1))
    (S : Finset (Fin (n + n + 1 + 1))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TwistedArrowHasUpperLeft i (insert (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowSupportPivot i S) S) ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TwistedArrowHasUpperLeft i S := by
  classical
  constructor
  · rintro ⟨j, hj, hS⟩
    refine ⟨j, hj, ?_⟩
    exact (Finset.mem_insert.mp hS).resolve_left
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowSupportPivot_ne_left i j (ne_of_gt hj) S)
  · rintro ⟨j, hj, hS⟩
    exact ⟨j, hj, Finset.mem_insert_of_mem hS⟩

/-- 選んだ点の削除も、左右の分岐条件を変えない。 -/
lemma twistedArrowHasUpperLeft_erase_pivot_iff {n : ℕ} (i : Fin (n + 1))
    (S : Finset (Fin (n + n + 1 + 1))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TwistedArrowHasUpperLeft i (S.erase (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowSupportPivot i S)) ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TwistedArrowHasUpperLeft i S := by
  classical
  constructor
  · rintro ⟨j, hj, hS⟩
    exact ⟨j, hj, Finset.mem_of_mem_erase hS⟩
  · rintro ⟨j, hj, hS⟩
    exact ⟨j, hj, Finset.mem_erase.mpr
      ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowSupportPivot_ne_left i j (ne_of_gt hj) S, hS⟩⟩

/-- 挿入後も同じ点が選ばれる。 -/
lemma twistedArrowSupportPivot_insert {n : ℕ} (i : Fin (n + 1))
    (S : Finset (Fin (n + n + 1 + 1))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowSupportPivot i (insert (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowSupportPivot i S) S) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowSupportPivot i S := by
  classical
  exact congrArg (fun p : Prop ↦ if p then _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeftVertex n i
    else _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRightVertex n i) (propext (twistedArrowHasUpperLeft_insert_pivot_iff i S))

/-- 削除後も同じ点が選ばれる。 -/
lemma twistedArrowSupportPivot_erase {n : ℕ} (i : Fin (n + 1))
    (S : Finset (Fin (n + n + 1 + 1))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowSupportPivot i (S.erase (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowSupportPivot i S)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowSupportPivot i S := by
  classical
  exact congrArg (fun p : Prop ↦ if p then _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeftVertex n i
    else _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRightVertex n i) (propext (twistedArrowHasUpperLeft_erase_pivot_iff i S))

/-- 領域外の頂点集合への挿入は、同じ領域外に留まる。 -/
lemma twistedArrowSupport_insert_notInDomain {n : ℕ} (i : Fin (n + 1))
    (S : Finset (Fin (n + n + 1 + 1))) (hS : ¬ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TwistedArrowSupportInDomain i S) :
    ¬ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TwistedArrowSupportInDomain i (insert (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowSupportPivot i S) S) := by
  classical
  obtain ⟨⟨a, ha, ha'⟩, ⟨b, hb, hb'⟩, hp⟩ :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.not_twistedArrowSupportInDomain_iff i S).mp hS
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.not_twistedArrowSupportInDomain_iff _ _).mpr
  refine ⟨⟨a, Finset.mem_insert_of_mem ha, ha'⟩,
    ⟨b, Finset.mem_insert_of_mem hb, hb'⟩, fun j hj ↦ ?_⟩
  exact (hp j hj).imp Finset.mem_insert_of_mem Finset.mem_insert_of_mem

/-- 左ホーンの領域外の集合からの削除も、同じ領域外に留まる。 -/
lemma twistedArrowSupport_erase_notInDomain {n : ℕ} (i : Fin (n + 1))
    (hi : i < Fin.last n) (S : Finset (Fin (n + n + 1 + 1)))
    (hS : ¬ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TwistedArrowSupportInDomain i S) :
    ¬ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TwistedArrowSupportInDomain i (S.erase (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowSupportPivot i S)) := by
  classical
  obtain ⟨a, ha, b, hb, hap, hpb⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowSupportPivot_interior i hi S hS
  have hpair := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.not_twistedArrowSupportInDomain_iff i S).mp hS |>.2.2
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.not_twistedArrowSupportInDomain_iff _ _).mpr
  have haS := Finset.mem_erase.mpr ⟨ne_of_lt hap, ha⟩
  have hbS := Finset.mem_erase.mpr ⟨ne_of_gt hpb, hb⟩
  have hleft : ∃ l ∈ S.erase (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowSupportPivot i S), l.val ≤ n := by
    by_cases h : a.val ≤ n
    · exact ⟨a, haS, h⟩
    · have ⟨⟨l, hl, hl'⟩, _, _⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.not_twistedArrowSupportInDomain_iff i S).mp hS
      refine ⟨l, Finset.mem_erase.mpr ⟨?_, hl⟩, hl'⟩
      intro heq
      have := congrArg Fin.val heq
      change a.val < (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowSupportPivot i S).val at hap
      omega
  have hright : ∃ r ∈ S.erase (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowSupportPivot i S), n < r.val := by
    by_cases h : n < b.val
    · exact ⟨b, hbS, h⟩
    · have ⟨_, ⟨r, hr, hr'⟩, _⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.not_twistedArrowSupportInDomain_iff i S).mp hS
      refine ⟨r, Finset.mem_erase.mpr ⟨?_, hr⟩, hr'⟩
      intro heq
      have := congrArg Fin.val heq
      change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowSupportPivot i S).val < b.val at hpb
      omega
  refine ⟨hleft, hright, fun j hj ↦ ?_⟩
  exact (hpair j hj).imp
    (fun h ↦ Finset.mem_erase.mpr ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowSupportPivot_ne_left i j hj S, h⟩)
    (fun h ↦ Finset.mem_erase.mpr ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowSupportPivot_ne_right i j hj S, h⟩)

/-- 内部の挿入点を欠く集合と含む集合の全単射。挿入と削除が互いに逆となる。 -/
def twistedArrowSupportPairEquiv {n : ℕ} (i : Fin (n + 1)) (hi : i < Fin.last n) :
    {S : Finset (Fin (n + n + 1 + 1)) //
      ¬ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TwistedArrowSupportInDomain i S ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowSupportPivot i S ∉ S} ≃
    {S : Finset (Fin (n + n + 1 + 1)) //
      ¬ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TwistedArrowSupportInDomain i S ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowSupportPivot i S ∈ S} := by
  classical
  exact
    { toFun := fun S ↦ ⟨insert (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowSupportPivot i S.val) S.val,
        twistedArrowSupport_insert_notInDomain i S.val S.property.1, by
          rw [twistedArrowSupportPivot_insert]
          exact Finset.mem_insert_self _ _⟩
      invFun := fun S ↦ ⟨S.val.erase (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowSupportPivot i S.val),
        twistedArrowSupport_erase_notInDomain i hi S.val S.property.1, by
          rw [twistedArrowSupportPivot_erase]
          exact Finset.notMem_erase _ _⟩
      left_inv := fun S ↦ by
        apply Subtype.ext
        change (insert (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowSupportPivot i S.val) S.val).erase
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowSupportPivot i (insert (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowSupportPivot i S.val) S.val)) = S.val
        rw [twistedArrowSupportPivot_insert, Finset.erase_insert S.property.2]
      right_inv := fun S ↦ by
        apply Subtype.ext
        change insert (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowSupportPivot i (S.val.erase (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowSupportPivot i S.val)))
          (S.val.erase (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowSupportPivot i S.val)) = S.val
        rw [twistedArrowSupportPivot_erase, Finset.insert_erase S.property.2] }

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
