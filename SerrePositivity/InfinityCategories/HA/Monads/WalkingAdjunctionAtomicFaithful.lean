module

public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionAtomicCancellation

/-!
概要：全次数の原子的な射の自由な道と実全射の比較は忠実である。
方針：先頭の原子と残りの回収を使い、道の長さに関する強い帰納法で示す。
規約：自由な道の全射性だけから忠実性を推定しない。
使われ方：Riehl–Verity Definition 2.1.4・Proposition 3.1.10、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）の前の全随伴の自由な生成。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace SerrePositivity.InfinityCategories.HA.Monads

variable {n : ℕ}

/-- 概要：原子的な一段の道の実像は元の実射。
方針：自由な道の延長の定義を使う。規約：同じ生成quiver。
使われ方：Riehl–Verity Proposition 3.1.10 の先頭の回収。 -/
lemma walkingAdjunctionAtomicPathFunctor_generator
    {A B : WalkingAdjunctionAtomicVertex n} (e : A ⟶ B) :
    (walkingAdjunctionAtomicPathFunctor n).map e.toPath = e.val :=
  Paths.lift_toPath (walkingAdjunctionAtomicPrefunctor n) e

/-- 概要：原子で終わる道の実像は正の長さを持つ。
方針：実合成の長さの加法性と原子の正の長さを使う。
規約：最後の実原子を使う。使われ方：Riehl–Verity Proposition 3.1.10 の単位の検出。 -/
lemma walkingAdjunctionAtomicPathFunctor_cons_size
    {A B C : WalkingAdjunctionAtomicVertex n} (p : Quiver.Path A B) (e : B ⟶ C) :
    0 < walkingAdjunctionLevelSize ((walkingAdjunctionAtomicPathFunctor n).map (p.cons e)) := by
  change 0 < walkingAdjunctionLevelSize
    (((walkingAdjunctionAtomicPathFunctor n).map p).prod' e.val ⋙
      walkingAdjunctionHorizontal A.level.point B.level.point C.level.point)
  have hs := walkingAdjunctionLevelSize_comp A.level.point B.level.point C.level.point
    ((walkingAdjunctionAtomicPathFunctor n).map p) e.val
  have hpos : 0 < walkingAdjunctionLevelSize ((walkingAdjunctionAtomicPathFunctor n).map p) +
      walkingAdjunctionLevelSize e.val := by
    have he := e.property.1
    omega
  exact hs.symm ▸ hpos

/-- 概要：空でない原子的な道の実像は正の長さを持つ。
方針：道の末尾を場合分けする。規約：同じ実像の長さ。
使われ方：Riehl–Verity Proposition 3.1.10 の空の道の回収。 -/
lemma walkingAdjunctionAtomicPathFunctor_size_pos
    {A B : WalkingAdjunctionAtomicVertex n} (p : Quiver.Path A B) (hp : 0 < p.length) :
    0 < walkingAdjunctionLevelSize ((walkingAdjunctionAtomicPathFunctor n).map p) := by
  cases p with
  | nil => simp only [Quiver.Path.length] at hp; omega
  | cons p e => exact walkingAdjunctionAtomicPathFunctor_cons_size p e

/-- 概要：同じ実像を持つ二つの原子的な道は同じ道である。
方針：先頭の実原子と残りを回収し、短い道に強い帰納法を使う。
規約：任意の二点・全次数・全ての有限の道。使われ方：Riehl–Verity Proposition 3.1.10。 -/
lemma walkingAdjunctionAtomicPathFunctor_map_injective
    {A B : WalkingAdjunctionAtomicVertex n} (p q : Quiver.Path A B)
    (h : (walkingAdjunctionAtomicPathFunctor n).map p =
      (walkingAdjunctionAtomicPathFunctor n).map q) : p = q := by
  suffices ∀ k, ∀ {A B : WalkingAdjunctionAtomicVertex n} (p q : Quiver.Path A B),
      p.length = k → (walkingAdjunctionAtomicPathFunctor n).map p =
        (walkingAdjunctionAtomicPathFunctor n).map q → p = q from this _ p q rfl h
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro A B p q hp hmap
    cases k with
    | zero =>
      have hAB := p.eq_of_length_zero hp
      subst B
      have hpnil := p.eq_nil_of_length_zero hp
      subst p
      cases q with
      | nil => rfl
      | cons q e =>
        have hpos := walkingAdjunctionAtomicPathFunctor_cons_size q e
        have hz : walkingAdjunctionLevelSize
            ((walkingAdjunctionAtomicPathFunctor n).map (Quiver.Path.nil (a := A))) = 0 :=
          walkingAdjunctionLevelSize_id n A.level.point
        rw [← hmap, hz] at hpos
        omega
    | succ k =>
      obtain ⟨C, e, p', hp', rfl⟩ := p.eq_toPath_comp_of_length_eq_succ hp
      have hqpos : q.length ≠ 0 := by
        intro hq
        have hAB := q.eq_of_length_zero hq
        subst B
        have hqnil := q.eq_nil_of_length_zero hq
        subst q
        have hpos := walkingAdjunctionAtomicPathFunctor_size_pos (e.toPath.comp p') (by
          rw [Quiver.Path.length_comp, Quiver.Path.length_toPath]
          omega)
        have hz : walkingAdjunctionLevelSize
            ((walkingAdjunctionAtomicPathFunctor n).map (Quiver.Path.nil (a := A))) = 0 :=
          walkingAdjunctionLevelSize_id n A.level.point
        rw [hmap, hz] at hpos
        omega
      obtain ⟨l, hl⟩ := Nat.exists_eq_succ_of_ne_zero hqpos
      obtain ⟨D, f, q', hq', rfl⟩ := q.eq_toPath_comp_of_length_eq_succ hl
      have hc : e.val ≫ (walkingAdjunctionAtomicPathFunctor n).map p' =
          f.val ≫ (walkingAdjunctionAtomicPathFunctor n).map q' := by
        calc
          _ = (walkingAdjunctionAtomicPathFunctor n).map e.toPath ≫
              (walkingAdjunctionAtomicPathFunctor n).map p' :=
            congrArg (fun u => u ≫ (walkingAdjunctionAtomicPathFunctor n).map p')
              (walkingAdjunctionAtomicPathFunctor_generator e).symm
          _ = (walkingAdjunctionAtomicPathFunctor n).map (e.toPath.comp p') :=
            ((walkingAdjunctionAtomicPathFunctor n).map_comp e.toPath p').symm
          _ = (walkingAdjunctionAtomicPathFunctor n).map (f.toPath.comp q') := hmap
          _ = (walkingAdjunctionAtomicPathFunctor n).map f.toPath ≫
              (walkingAdjunctionAtomicPathFunctor n).map q' :=
            (walkingAdjunctionAtomicPathFunctor n).map_comp f.toPath q'
          _ = _ := congrArg (fun u => u ≫ (walkingAdjunctionAtomicPathFunctor n).map q')
            (walkingAdjunctionAtomicPathFunctor_generator f)
      obtain ⟨hCD, hef, ht⟩ := walkingAdjunctionAtomicLeftCancellation
        e.val f.val ((walkingAdjunctionAtomicPathFunctor n).map p')
        ((walkingAdjunctionAtomicPathFunctor n).map q') e.property f.property hc
      have hCD' : C = D := by
        cases C
        cases D
        cases hCD
        rfl
      subst D
      have hef' : e = f := Subtype.ext (eq_of_heq hef)
      subst f
      have hpq := ih k (Nat.lt_succ_self k) p' q' hp' (eq_of_heq ht)
      cases hpq
      rfl

/-- 概要：全次数の原子的な自由な道から実全射への比較関手は忠実。
方針：全ての道での像の単射性を使う。規約：instanceを実証明から構成する。
使われ方：Riehl–Verity Proposition 3.1.10 の各次数の自由性。 -/
instance walkingAdjunctionAtomicPathFunctor_faithful (n : ℕ) :
    (walkingAdjunctionAtomicPathFunctor n).Faithful where
  map_injective := by
    intro A B p q h
    exact walkingAdjunctionAtomicPathFunctor_map_injective p q h

end SerrePositivity.InfinityCategories.HA.Monads
