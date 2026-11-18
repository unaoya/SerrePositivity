module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.AugmentedNerve
public import Mathlib.CategoryTheory.Join.Basic

/-!
概要：二つの nerve の join の同じ単体を、通常圏の join の射列として読む。
方針：切断の前後で元の二つの射列を使い、またぐ射は join の唯一の射とする。
規約：空の前半・後半を許し、元の圏の非空性を要求しない。
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

/-- 前半の頂点の同じ添字。HTT 1.2.8、Kerodon §4.3.2（Tag 0160）。 -/
def nerveJoinLeftIndex {n : ℕ} (s : Join.Simplex (nerve C) (nerve D) n)
    (i : Fin (n + 1)) (hi : i.val < s.1.val) : Fin s.1.val := ⟨i.val, hi⟩

/-- 後半の頂点の原点を切断へ移す。HTT 1.2.8、Kerodon §4.3.2（Tag 0160）。 -/
def nerveJoinRightIndex {n : ℕ} (s : Join.Simplex (nerve C) (nerve D) n)
    (i : Fin (n + 1)) (hi : ¬ i.val < s.1.val) : Fin (n + 1 - s.1.val) :=
  ⟨i.val - s.1.val, by have := i.isLt; omega⟩

/-- 元の二つの射列の頂点を通常の join へ包含する。
HTT 1.2.8、Kerodon §4.3.2（Tag 0160）、同じ切断の対象写像。 -/
def nerveJoinObj {n : ℕ} (s : Join.Simplex (nerve C) (nerve D) n)
    (i : Fin (n + 1)) : CategoryTheory.Join C D :=
  if hi : i.val < s.1.val then
    CategoryTheory.Join.left (augNerveObj s.2.1 (nerveJoinLeftIndex s i hi))
  else CategoryTheory.Join.right (augNerveObj s.2.2 (nerveJoinRightIndex s i hi))

/-- 前半の対象は元の左射列の同じ頂点。HTT 1.2.8、Kerodon §4.3.2（Tag 0160）。 -/
lemma nerveJoinObj_left {n : ℕ} (s : Join.Simplex (nerve C) (nerve D) n)
    (i : Fin (n + 1)) (hi : i.val < s.1.val) :
    nerveJoinObj s i = CategoryTheory.Join.left (augNerveObj s.2.1 (nerveJoinLeftIndex s i hi)) := by
  simp only [nerveJoinObj, dite_eq_left hi]

/-- 後半の対象は元の右射列の同じ頂点。HTT 1.2.8、Kerodon §4.3.2（Tag 0160）。 -/
lemma nerveJoinObj_right {n : ℕ} (s : Join.Simplex (nerve C) (nerve D) n)
    (i : Fin (n + 1)) (hi : ¬ i.val < s.1.val) :
    nerveJoinObj s i = CategoryTheory.Join.right (augNerveObj s.2.2 (nerveJoinRightIndex s i hi)) := by
  simp only [nerveJoinObj, dite_eq_right hi]

/-- 同じ側の射は元の射列の射、交差射は通常の join の指定射。
HTT 1.2.8、Kerodon §4.3.2（Tag 0160）、通常の join への射の表示。 -/
def nerveJoinMap {n : ℕ} (s : Join.Simplex (nerve C) (nerve D) n)
    {i j : Fin (n + 1)} (h : i ≤ j) : nerveJoinObj s i ⟶ nerveJoinObj s j :=
  if hi : i.val < s.1.val then
    if hj : j.val < s.1.val then
      eqToHom (nerveJoinObj_left s i hi) ≫
        (CategoryTheory.Join.inclLeft C D).map
          (augNerveMap s.2.1 (show nerveJoinLeftIndex s i hi ≤ nerveJoinLeftIndex s j hj from h)) ≫
        eqToHom (nerveJoinObj_left s j hj).symm
    else
      eqToHom (nerveJoinObj_left s i hi) ≫
        CategoryTheory.Join.edge _ _ ≫ eqToHom (nerveJoinObj_right s j hj).symm
  else
    have hj : ¬ j.val < s.1.val := fun hj => hi (lt_of_le_of_lt h hj)
    eqToHom (nerveJoinObj_right s i hi) ≫
      (CategoryTheory.Join.inclRight C D).map
        (augNerveMap s.2.2 (Nat.sub_le_sub_right h s.1.val)) ≫
      eqToHom (nerveJoinObj_right s j hj).symm

/-- join の射列表示は恒等射を保つ。HTT 1.2.8、Kerodon §4.3.2（Tag 0160）。 -/
lemma nerveJoinMap_id {n : ℕ} (s : Join.Simplex (nerve C) (nerve D) n)
    (i : Fin (n + 1)) : nerveJoinMap s (le_refl i) = 𝟙 (nerveJoinObj s i) := by
  by_cases hi : i.val < s.1.val
  · simp only [nerveJoinMap, dite_eq_left hi, augNerveMap_id, CategoryTheory.Functor.map_id]
    change eqToHom (nerveJoinObj_left s i hi) ≫
      𝟙 (CategoryTheory.Join.left (augNerveObj s.2.1 (nerveJoinLeftIndex s i hi))) ≫
        eqToHom (nerveJoinObj_left s i hi).symm = 𝟙 (nerveJoinObj s i)
    simp only [Category.id_comp, eqToHom_trans, eqToHom_refl]
  · simp only [nerveJoinMap, dite_eq_right hi, augNerveMap_id, CategoryTheory.Functor.map_id]
    change eqToHom (nerveJoinObj_right s i hi) ≫
      𝟙 (CategoryTheory.Join.right (augNerveObj s.2.2 (nerveJoinRightIndex s i hi))) ≫
        eqToHom (nerveJoinObj_right s i hi).symm = 𝟙 (nerveJoinObj s i)
    simp only [Category.id_comp, eqToHom_trans, eqToHom_refl]

/-- join の射列表示は合成を保つ。
HTT 1.2.8、Kerodon §4.3.2（Tag 0160）。交差射の一意性以外は元の合成則だけを使う。 -/
lemma nerveJoinMap_comp {n : ℕ} (s : Join.Simplex (nerve C) (nerve D) n)
    {i j k : Fin (n + 1)} (hij : i ≤ j) (hjk : j ≤ k) :
    nerveJoinMap s (hij.trans hjk) = nerveJoinMap s hij ≫ nerveJoinMap s hjk := by
  by_cases hi : i.val < s.1.val
  · by_cases hk : k.val < s.1.val
    · have hj : j.val < s.1.val := lt_of_le_of_lt hjk hk
      simp only [nerveJoinMap, dite_eq_left hi, dite_eq_left hj, dite_eq_left hk]
      simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
      rw [← CategoryTheory.Functor.map_comp_assoc, ← augNerveMap_comp]
    · have : Subsingleton (nerveJoinObj s i ⟶ nerveJoinObj s k) := by
        rw [nerveJoinObj_left s i hi, nerveJoinObj_right s k hk]
        infer_instance
      exact Subsingleton.elim _ _
  · have hj : ¬ j.val < s.1.val := fun hj => hi (lt_of_le_of_lt hij hj)
    have hk : ¬ k.val < s.1.val := fun hk => hj (lt_of_le_of_lt hjk hk)
    simp only [nerveJoinMap, dite_eq_right hi, dite_eq_right hj, dite_eq_right hk]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    rw [← CategoryTheory.Functor.map_comp_assoc, ← augNerveMap_comp]

/-- 元の join の単体を、通常圏の join の同じ全射列に読む。
HTT 1.2.8、Kerodon §4.3.2（Tag 0160）。単体的自然性は別に検証する。 -/
def nerveJoinChain {n : ℕ} (s : Join.Simplex (nerve C) (nerve D) n) :
    ComposableArrows (CategoryTheory.Join C D) n where
  obj := nerveJoinObj s
  map f := nerveJoinMap s (leOfHom f)
  map_id := nerveJoinMap_id s
  map_comp f g := nerveJoinMap_comp s (leOfHom f) (leOfHom g)

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
