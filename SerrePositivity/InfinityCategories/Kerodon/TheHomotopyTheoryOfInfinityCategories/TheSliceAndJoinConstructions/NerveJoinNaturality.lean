module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.NerveJoinChains

/-!
概要：元の二つの nerve の join から通常圏の join の nerve への全単体的比較。
方針：切断と左右の射列の再添字を比較し、同じ射列の読み方を単体的射へ束ねる。
規約：面と退化を同時に扱い、空の左右の因子を許す。
使われ方：HTT 1.2.8、Kerodon §4.3.2（Tag 0160）、S8 の指定 Yoneda の模型比較の法則。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
variable {C D : Type u} [SmallCategory C] [SmallCategory D]

/-- 左半分の添字は元の順序写像の左制限で写る。
HTT 1.2.8、Kerodon §4.3.2（Tag 0160）、切断の再添字則。 -/
lemma nerveJoinLeftIndex_simplexMap {m n : ℕ}
    (α : Fin (m + 1) →o Fin (n + 1)) (s : Join.Simplex (nerve C) (nerve D) n)
    (i : Fin (m + 1)) (hi : i.val < Join.pullCut α s.1.val) :
    Join.leftMap α s.1.val (nerveJoinLeftIndex (Join.simplexMap _ _ α s) i hi) =
      nerveJoinLeftIndex s (α i) ((Join.lt_pullCut_iff α s.1.val i).mp hi) := by
  apply Fin.ext
  rfl

/-- 右半分の原点移動した添字は、元の順序写像の右制限で写る。
HTT 1.2.8、Kerodon §4.3.2（Tag 0160）、切断の再添字則。 -/
lemma nerveJoinRightIndex_simplexMap {m n : ℕ}
    (α : Fin (m + 1) →o Fin (n + 1)) (s : Join.Simplex (nerve C) (nerve D) n)
    (i : Fin (m + 1)) (hi : ¬ i.val < Join.pullCut α s.1.val) :
    Join.rightMap α s.1.val (nerveJoinRightIndex (Join.simplexMap _ _ α s) i hi) =
      nerveJoinRightIndex s (α i) (fun h => hi ((Join.lt_pullCut_iff α s.1.val i).mpr h)) := by
  apply Fin.ext
  change (α ⟨Join.pullCut α s.1.val + (i.val - Join.pullCut α s.1.val), by have := i.isLt; omega⟩).val -
      s.1.val = (α i).val - s.1.val
  have he : (⟨Join.pullCut α s.1.val + (i.val - Join.pullCut α s.1.val), by have := i.isLt; omega⟩ :
      Fin (m + 1)) = i := by apply Fin.ext; dsimp; omega
  rw [he]

/-- 同じ join の対象の読み方は全順序写像と可換。
HTT 1.2.8、Kerodon §4.3.2（Tag 0160）、全射列の対象の自然性。 -/
lemma nerveJoinObj_simplexMap {m n : ℕ}
    (α : Fin (m + 1) →o Fin (n + 1)) (s : Join.Simplex (nerve C) (nerve D) n)
    (i : Fin (m + 1)) :
    nerveJoinObj (Join.simplexMap _ _ α s) i = nerveJoinObj s (α i) := by
  by_cases hi : i.val < Join.pullCut α s.1.val
  · have ha := (Join.lt_pullCut_iff α s.1.val i).mp hi
    rw [nerveJoinObj_left _ i hi, nerveJoinObj_left s (α i) ha]
    congr 1
    change augNerveObj (Join.augMap (nerve C) (Join.leftMap α s.1.val) s.2.1) _ = _
    rw [augNerveObj_augMap, nerveJoinLeftIndex_simplexMap]
  · have ha : ¬ (α i).val < s.1.val :=
      fun h => hi ((Join.lt_pullCut_iff α s.1.val i).mpr h)
    rw [nerveJoinObj_right _ i hi, nerveJoinObj_right s (α i) ha]
    congr 1
    change augNerveObj (Join.augMap (nerve D) (Join.rightMap α s.1.val) s.2.2) _ = _
    rw [augNerveObj_augMap, nerveJoinRightIndex_simplexMap]

private lemma augMap_heq {A : Type u} [SmallCategory A] {m r : ℕ}
    (α : Fin m →o Fin r) (s : Join.augObj (nerve A) r) {i j : Fin m} (h : i ≤ j) :
    HEq (augNerveMap (Join.augMap (nerve A) α s) h) (augNerveMap s (α.monotone h)) := by
  cases m with
  | zero => exact Fin.elim0 i
  | succ m => cases r with
    | zero => exact Fin.elim0 (α i)
    | succ r => rfl

private lemma augIndex_heq {A : Type u} [SmallCategory A] {r : ℕ}
    (s : Join.augObj (nerve A) r) {i j i' j' : Fin r}
    (hi : i = i') (hj : j = j') (h : i ≤ j) (h' : i' ≤ j') :
    HEq (augNerveMap s h) (augNerveMap s h') := by
  subst i' j'
  rfl

private lemma functorMap_heq {A B : Type u} [SmallCategory A] [SmallCategory B]
    (F : A ⥤ B) {a b c d : A} (ha : a = c) (hb : b = d)
    (f : a ⟶ b) (g : c ⟶ d) (hf : HEq f g) : HEq (F.map f) (F.map g) := by
  subst c d
  exact heq_of_eq (congrArg F.map (eq_of_heq hf))

/-- 同じ join の射の読み方も、全順序写像に対して端点の移送を介して可換。
HTT 1.2.8、Kerodon §4.3.2（Tag 0160）、全射列の射の自然性。 -/
lemma nerveJoinMap_simplexMap {m n : ℕ}
    (α : Fin (m + 1) →o Fin (n + 1)) (s : Join.Simplex (nerve C) (nerve D) n)
    {i j : Fin (m + 1)} (h : i ≤ j) :
    HEq (nerveJoinMap (Join.simplexMap _ _ α s) h) (nerveJoinMap s (α.monotone h)) := by
  by_cases hi : i.val < Join.pullCut α s.1.val
  · have ha := (Join.lt_pullCut_iff α s.1.val i).mp hi
    by_cases hj : j.val < Join.pullCut α s.1.val
    · have hb := (Join.lt_pullCut_iff α s.1.val j).mp hj
      have hi' : i.val < (Join.simplexMap (nerve C) (nerve D) α s).1.val := hi
      have hj' : j.val < (Join.simplexMap (nerve C) (nerve D) α s).1.val := hj
      simp only [nerveJoinMap, dite_eq_left hi', dite_eq_left hj', dite_eq_left ha, dite_eq_left hb,
        eqToHom_comp_heq_iff, comp_eqToHom_heq_iff,
        heq_eqToHom_comp_iff, heq_comp_eqToHom_iff]
      apply functorMap_heq (CategoryTheory.Join.inclLeft C D)
      · exact (augNerveObj_augMap _ _ _).trans
          (congrArg (augNerveObj s.2.1) (nerveJoinLeftIndex_simplexMap α s i hi))
      · exact (augNerveObj_augMap _ _ _).trans
          (congrArg (augNerveObj s.2.1) (nerveJoinLeftIndex_simplexMap α s j hj))
      · exact (augMap_heq _ _ _).trans
          (augIndex_heq s.2.1 (nerveJoinLeftIndex_simplexMap α s i hi)
            (nerveJoinLeftIndex_simplexMap α s j hj) _ _)
    · apply (conj_eqToHom_iff_heq _ _ (nerveJoinObj_simplexMap α s i)
        (nerveJoinObj_simplexMap α s j)).mp
      have : Subsingleton (nerveJoinObj (Join.simplexMap _ _ α s) i ⟶
          nerveJoinObj (Join.simplexMap _ _ α s) j) := by
        rw [nerveJoinObj_left _ i hi, nerveJoinObj_right _ j hj]
        infer_instance
      exact Subsingleton.elim _ _
  · have ha : ¬ (α i).val < s.1.val :=
      fun hh => hi ((Join.lt_pullCut_iff α s.1.val i).mpr hh)
    have hj : ¬ j.val < Join.pullCut α s.1.val := fun hh => hi (lt_of_le_of_lt h hh)
    have hb : ¬ (α j).val < s.1.val :=
      fun hh => hj ((Join.lt_pullCut_iff α s.1.val j).mpr hh)
    have hi' : ¬ i.val < (Join.simplexMap (nerve C) (nerve D) α s).1.val := hi
    have hj' : ¬ j.val < (Join.simplexMap (nerve C) (nerve D) α s).1.val := hj
    simp only [nerveJoinMap, dite_eq_right hi', dite_eq_right hj', dite_eq_right ha, dite_eq_right hb,
      eqToHom_comp_heq_iff, comp_eqToHom_heq_iff,
      heq_eqToHom_comp_iff, heq_comp_eqToHom_iff]
    apply functorMap_heq (CategoryTheory.Join.inclRight C D)
    · exact (augNerveObj_augMap _ _ _).trans
        (congrArg (augNerveObj s.2.2) (nerveJoinRightIndex_simplexMap α s i hi))
    · exact (augNerveObj_augMap _ _ _).trans
        (congrArg (augNerveObj s.2.2) (nerveJoinRightIndex_simplexMap α s j hj))
    · exact (augMap_heq _ _ _).trans
        (augIndex_heq s.2.2 (nerveJoinRightIndex_simplexMap α s i hi)
          (nerveJoinRightIndex_simplexMap α s j hj) _ _)

/-- 同じ全射列の読み方は、面・退化の全てと厳密に可換。
HTT 1.2.8、Kerodon §4.3.2（Tag 0160）、nerve と join の比較射の自然性。 -/
lemma nerveJoinChain_simplexMap {m n : ℕ}
    (α : Fin (m + 1) →o Fin (n + 1)) (s : Join.Simplex (nerve C) (nerve D) n) :
    nerveJoinChain (Join.simplexMap _ _ α s) = α.toFunctor ⋙ nerveJoinChain s := by
  refine CategoryTheory.Functor.hext (nerveJoinObj_simplexMap α s) ?_
  intro i j h
  exact nerveJoinMap_simplexMap α s (leOfHom h)

/-- 二つの元の nerve の join を、通常圏の join の nerve へ同じ全射列で送る。
HTT 1.2.8、Kerodon §4.3.2（Tag 0160）、S8 の指定 Yoneda の模型比較の入力。 -/
def nerveJoinComparison (C D : Type u) [SmallCategory C] [SmallCategory D] :
    join (nerve C) (nerve D) ⟶ nerve (CategoryTheory.Join C D) where
  app _ := ↾nerveJoinChain
  naturality {n m} α := by
    apply ConcreteCategory.hom_ext
    intro s
    exact nerveJoinChain_simplexMap α.unop.toOrderHom s

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
