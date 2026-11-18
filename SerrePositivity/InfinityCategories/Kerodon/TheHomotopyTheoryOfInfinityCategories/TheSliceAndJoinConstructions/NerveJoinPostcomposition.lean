module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.NerveJoinNaturality

/-!
概要：nerve と join の比較は、左右の係数関手による後合成と可換である。
方針：空単体を含む全射列を対象と射で比較し、移送を介した等式を束ねる。
規約：比較射を展開せず、指定した同じ切断を保つ。
使われ方：HTT 1.2.8、Kerodon §4.3.2（Tag 0160）、S8 の全 Hom 図式の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
variable {C D C' D' : Type u} [SmallCategory C] [SmallCategory D]
  [SmallCategory C'] [SmallCategory D']

/-- 空の添字を許した nerve の対象の評価は係数関手と可換。
HTT 1.2.8、Kerodon §4.3.2（Tag 0160）、模型比較の後合成則。 -/
lemma augNerveObj_postcomp (F : C ⥤ C') {r : ℕ}
    (s : Join.augObj (nerve C) r) (i : Fin r) :
    augNerveObj (Join.augHom (nerveMap F) r s) i = F.obj (augNerveObj s i) := by
  cases r with
  | zero => exact Fin.elim0 i
  | succ r => rfl

/-- 空の添字を許した nerve の射の評価は係数関手と移送を介して可換。
HTT 1.2.8、Kerodon §4.3.2（Tag 0160）、模型比較の後合成則。 -/
lemma augNerveMap_postcomp (F : C ⥤ C') {r : ℕ}
    (s : Join.augObj (nerve C) r) {i j : Fin r} (h : i ≤ j) :
    HEq (augNerveMap (Join.augHom (nerveMap F) r s) h) (F.map (augNerveMap s h)) := by
  cases r with
  | zero => exact Fin.elim0 i
  | succ r => rfl

/-- join の同じ切断での対象の評価は左右の関手と可換。
HTT 1.2.8、Kerodon §4.3.2（Tag 0160）、模型比較の後合成則。 -/
lemma nerveJoinObj_postcomp (F : C ⥤ C') (G : D ⥤ D') {n : ℕ}
    (s : Join.Simplex (nerve C) (nerve D) n) (i : Fin (n + 1)) :
    nerveJoinObj ((joinMap (nerveMap F) (nerveMap G)).app (Opposite.op ⦋n⦌) s) i =
      (CategoryTheory.Join.mapPair F G).obj (nerveJoinObj s i) := by
  by_cases hi : i.val < s.1.val
  · rw [nerveJoinObj_left ((joinMap (nerveMap F) (nerveMap G)).app (Opposite.op ⦋n⦌) s) i hi, nerveJoinObj_left s i hi]
    exact congrArg CategoryTheory.Join.left (augNerveObj_postcomp F s.2.1 _)
  · rw [nerveJoinObj_right ((joinMap (nerveMap F) (nerveMap G)).app (Opposite.op ⦋n⦌) s) i hi, nerveJoinObj_right s i hi]
    exact congrArg CategoryTheory.Join.right (augNerveObj_postcomp G s.2.2 _)

private lemma map_heq {A B : Type u} [SmallCategory A] [SmallCategory B]
    (F : A ⥤ B) {a b c d : A} (ha : a = c) (hb : b = d)
    (f : a ⟶ b) (g : c ⟶ d) (hf : HEq f g) : HEq (F.map f) (F.map g) := by
  subst c d
  exact heq_of_eq (congrArg F.map (eq_of_heq hf))

/-- join の全射列の射は左右の関手と移送を介して可換。
HTT 1.2.8、Kerodon §4.3.2（Tag 0160）、模型比較の後合成則。 -/
lemma nerveJoinMap_postcomp (F : C ⥤ C') (G : D ⥤ D') {n : ℕ}
    (s : Join.Simplex (nerve C) (nerve D) n) {i j : Fin (n + 1)} (h : i ≤ j) :
    HEq (nerveJoinMap ((joinMap (nerveMap F) (nerveMap G)).app (Opposite.op ⦋n⦌) s) h)
      ((CategoryTheory.Join.mapPair F G).map (nerveJoinMap s h)) := by
  by_cases hi : i.val < s.1.val
  · by_cases hj : j.val < s.1.val
    · have hi' : i.val < ((joinMap (nerveMap F) (nerveMap G)).app (Opposite.op ⦋n⦌) s).1.val := hi
      have hj' : j.val < ((joinMap (nerveMap F) (nerveMap G)).app (Opposite.op ⦋n⦌) s).1.val := hj
      simp only [nerveJoinMap, dite_eq_left hi, dite_eq_left hj, dite_eq_left hi', dite_eq_left hj',
        CategoryTheory.Functor.map_comp, eqToHom_map,
        CategoryTheory.Join.mapPair_map_inclLeft, eqToHom_comp_heq_iff,
        comp_eqToHom_heq_iff, heq_eqToHom_comp_iff, heq_comp_eqToHom_iff]
      apply map_heq (CategoryTheory.Join.inclLeft C' D')
      · exact augNerveObj_postcomp F s.2.1 _
      · exact augNerveObj_postcomp F s.2.1 _
      · exact augNerveMap_postcomp F s.2.1 _
    · apply (conj_eqToHom_iff_heq _ _ (nerveJoinObj_postcomp F G s i)
        (nerveJoinObj_postcomp F G s j)).mp
      have : Subsingleton (nerveJoinObj ((joinMap (nerveMap F) (nerveMap G)).app (Opposite.op ⦋n⦌) s) i ⟶
          nerveJoinObj ((joinMap (nerveMap F) (nerveMap G)).app (Opposite.op ⦋n⦌) s) j) := by
        rw [nerveJoinObj_left ((joinMap (nerveMap F) (nerveMap G)).app (Opposite.op ⦋n⦌) s) i hi, nerveJoinObj_right ((joinMap (nerveMap F) (nerveMap G)).app (Opposite.op ⦋n⦌) s) j hj]
        infer_instance
      exact Subsingleton.elim _ _
  · have hj : ¬ j.val < s.1.val := fun hh => hi (lt_of_le_of_lt h hh)
    have hi' : ¬ i.val < ((joinMap (nerveMap F) (nerveMap G)).app (Opposite.op ⦋n⦌) s).1.val := hi
    have hj' : ¬ j.val < ((joinMap (nerveMap F) (nerveMap G)).app (Opposite.op ⦋n⦌) s).1.val := hj
    simp only [nerveJoinMap, dite_eq_right hi, dite_eq_right hj, dite_eq_right hi', dite_eq_right hj',
      CategoryTheory.Functor.map_comp, eqToHom_map,
      CategoryTheory.Join.mapPair_map_inclRight, eqToHom_comp_heq_iff,
      comp_eqToHom_heq_iff, heq_eqToHom_comp_iff, heq_comp_eqToHom_iff]
    apply map_heq (CategoryTheory.Join.inclRight C' D')
    · exact augNerveObj_postcomp G s.2.2 _
    · exact augNerveObj_postcomp G s.2.2 _
    · exact augNerveMap_postcomp G s.2.2 _

/-- nerve と join の全射列の比較は左右の係数関手の後合成を保つ。
HTT 1.2.8、Kerodon §4.3.2（Tag 0160）、模型比較の後合成則。 -/
lemma nerveJoinChain_postcomp (F : C ⥤ C') (G : D ⥤ D') {n : ℕ}
    (s : Join.Simplex (nerve C) (nerve D) n) :
    nerveJoinChain ((joinMap (nerveMap F) (nerveMap G)).app (Opposite.op ⦋n⦌) s) =
      nerveJoinChain s ⋙ CategoryTheory.Join.mapPair F G := by
  refine CategoryTheory.Functor.hext (nerveJoinObj_postcomp F G s) ?_
  intro i j h
  exact nerveJoinMap_postcomp F G s (leOfHom h)

/-- 比較射は左右の係数関手の全族に自然である。
HTT 1.2.8、Kerodon §4.3.2（Tag 0160）、S8 の全 Hom 図式の比較の法則。 -/
lemma nerveJoinComparison_naturality (F : C ⥤ C') (G : D ⥤ D') :
    joinMap (nerveMap F) (nerveMap G) ≫ nerveJoinComparison C' D' =
      nerveJoinComparison C D ≫ nerveMap (CategoryTheory.Join.mapPair F G) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  exact nerveJoinChain_postcomp F G s

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
