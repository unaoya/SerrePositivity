module

public import SerrePositivity.InfinityCategories.HA.Monads.OrdinalConcatenation
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.BooleanAlgebra
public import Mathlib.Data.Fintype.Card

/-!
概要：有限単調射の実像の個数と、合成した実像の個数の上下を比較する。
方針：有限像と中間集合内の補集合を使って合成で失う点の個数を押さえる。
規約：有限順序集合は空も含む。原典の文字列の幅との全比較は別に行う。
使われ方：Riehl–Verity Proposition 4.2.15の幅の実順序表示、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）の前の実filtrationの個数の照合。
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.InfinityCategories.HA.Monads

/-- 概要：有限単調射の実像の個数。
方針：全有限点の像の有限集合を取る。規約：空の像も含む。
使われ方：Riehl–Verity Proposition 4.2.15の実辺の幅の計算。 -/
def ordinalImageCard {m n : ℕ} (f : Fin m →o Fin n) : ℕ := (Finset.univ.image f).card

/-- 概要：実像の個数は実始点の個数以下。
方針：有限像の個数の上限。規約：空も含む。
使われ方：Riehl–Verity Proposition 4.2.15の実辺の変化量。 -/
lemma ordinalImageCard_le_source {m n : ℕ} (f : Fin m →o Fin n) : ordinalImageCard f ≤ m := by
  simpa only [ordinalImageCard, Finset.card_univ, Fintype.card_fin] using
    (Finset.card_image_le (s := Finset.univ) (f := f))

/-- 概要：実像の個数は実終点の個数以下。
方針：全有限集合への包含。規約：空も含む。
使われ方：Riehl–Verity Proposition 4.2.15の実辺の変化量。 -/
lemma ordinalImageCard_le_target {m n : ℕ} (f : Fin m →o Fin n) : ordinalImageCard f ≤ n := by
  simpa only [ordinalImageCard, Finset.card_univ, Fintype.card_fin] using
    (Finset.card_le_card (Finset.subset_univ (Finset.univ.image f)))

/-- 概要：実像の個数が実始点の個数と等しいことは単射性と同値。
方針：全有限集合上の像の個数の等式と単射性を比較する。
規約：有限順序の射そのものの単射性。使われ方：Riehl–Verity §4.2の変化量0の検収。 -/
lemma ordinalImageCard_eq_source_iff {m n : ℕ} (f : Fin m →o Fin n) :
    ordinalImageCard f = m ↔ Function.Injective f := by
  simpa only [ordinalImageCard, Finset.card_univ, Fintype.card_fin, Finset.coe_univ,
    Set.injOn_univ] using
    (Finset.card_image_iff (s := Finset.univ) (f := f))

/-- 概要：実像の個数が実終点の個数と等しいことは全射性と同値。
方針：像の有限集合が全体となることを個数の等式から回収する。
規約：有限順序の射そのものの全射性。使われ方：Riehl–Verity §4.2の実併合の検収。 -/
lemma ordinalImageCard_eq_target_iff {m n : ℕ} (f : Fin m →o Fin n) :
    ordinalImageCard f = n ↔ Function.Surjective f := by
  constructor
  · intro h
    have he : Finset.univ.image f = Finset.univ := Finset.eq_of_subset_of_card_le
      (Finset.subset_univ _) (by
        simpa only [ordinalImageCard, Finset.card_univ, Fintype.card_fin] using h.ge)
    intro y
    have hy : y ∈ Finset.univ.image f := he ▸ Finset.mem_univ y
    obtain ⟨x, _, hxy⟩ := Finset.mem_image.mp hy
    exact ⟨x, hxy⟩
  · intro h
    simp only [ordinalImageCard, Finset.image_univ_of_surjective h, Finset.card_univ,
      Fintype.card_fin]

/-- 概要：合成した実像と中間集合の個数は、元の二つの実像の個数の和以上。
方針：後半の実像を、前半の像とその補集合の像へ分けて個数を押さえる。
規約：空も許す任意の実二射。使われ方：Riehl–Verity §4.2の実面での変化量の比較。 -/
lemma ordinalImageCard_comp_lower_bound {a b c : ℕ} (f : Fin a →o Fin b) (g : Fin b →o Fin c) :
    ordinalImageCard f + ordinalImageCard g ≤ b + ordinalImageCard (g.comp f) := by
  let s : Finset (Fin b) := Finset.univ.image f
  have hu : s ∪ (Finset.univ \ s) = Finset.univ :=
    Finset.union_sdiff_of_subset (Finset.subset_univ s)
  have hi : Finset.univ.image g = s.image g ∪ (Finset.univ \ s).image g := by
    rw [← Finset.image_union, hu]
  have hcard := Finset.card_union_le (s.image g) ((Finset.univ \ s).image g)
  have hcomp : (s.image g).card = ordinalImageCard (g.comp f) := by
    simp only [s, ordinalImageCard, Finset.image_image]
    rfl
  have hrest := Finset.card_image_le (s := Finset.univ \ s) (f := g)
  have hsum := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ s)
  rw [← hi, hcomp] at hcard
  change ordinalImageCard g ≤ ordinalImageCard (g.comp f) + _ at hcard
  have hsum' : (Finset.univ \ s).card + ordinalImageCard f = b := by
    simpa only [s, ordinalImageCard, Finset.card_univ, Fintype.card_fin] using hsum
  omega

/-- 概要：前半が全射なら合成は後半の実像の個数を保つ。
方針：前半の像の有限集合が全体であることを使う。
規約：実射の合成の等式で比較する。使われ方：Riehl–Verity §4.2の実親の幅の保存。 -/
lemma ordinalImageCard_comp_of_surjective {a b c : ℕ} (f : Fin a →o Fin b)
    (g : Fin b →o Fin c) (hf : Function.Surjective f) :
    ordinalImageCard (g.comp f) = ordinalImageCard g := by
  have he : Finset.univ.image f = Finset.univ := Finset.image_univ_of_surjective hf
  calc
    ordinalImageCard (g.comp f) = ((Finset.univ.image f).image g).card := by
      simp only [ordinalImageCard, Finset.image_image]
      rfl
    _ = ordinalImageCard g := by rw [he]; rfl

end SerrePositivity.InfinityCategories.HA.Monads
