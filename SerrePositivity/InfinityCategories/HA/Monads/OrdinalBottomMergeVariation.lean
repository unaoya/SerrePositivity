module

public import SerrePositivity.InfinityCategories.HA.Monads.OrdinalMapVariation

/-!
概要：先行辺の像が値1を欠くと、底併合との合成は変化量を1減らす。
方針：一つだけの底併合は値1を欠く部分集合に単射であり、合成の像の個数が保たれる。
規約：実単調射とその全点での具体的な値の条件を使う。
使われ方：Riehl–Verity Proposition 4.2.15の指定直前の面の幅、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）の前の実filtrationの厳密な減少。
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.InfinityCategories.HA.Monads

/-- 概要：値1を欠く実像は、実底併合との合成で像の個数を保つ。
方針：底併合の二つの値の一致を調べ、値1を欠く実像上の単射性を示す。
規約：空の始点も含む。使われ方：Riehl–Verity §4.2の隣接する実面の幅の計算。 -/
lemma ordinalImageCard_comp_bottomMerge_of_no_one {a b c : ℕ}
    (f : Fin a →o Fin b) (g : Fin b →o Fin c)
    (hf : ∀ i, (f i).val ≠ 1) (hg : ∀ i, (g i).val = i.val - 1) :
    ordinalImageCard (g.comp f) = ordinalImageCard f := by
  classical
  have hinj : Set.InjOn g (↑(Finset.univ.image f) : Set (Fin b)) := by
    intro x hx y hy hxy
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hy
    have hi := hf i
    have hj := hf j
    have hv := congrArg (fun t : Fin c => t.val) hxy
    rw [hg, hg] at hv
    apply Fin.ext
    omega
  have he : (Finset.univ.image f).image g = Finset.univ.image (g.comp f) := by
    rw [Finset.image_image]
    rfl
  unfold ordinalImageCard
  rw [← he]
  exact Finset.card_image_iff.mpr hinj

/-- 概要：一つだけの実底併合の変化量は1。
方針：全点の値と個数から全射性を構成し、像の個数を終点へ戻す。
規約：両端の個数の等式を明示する。使われ方：Riehl–Verity §4.2の実幅の欠損。 -/
lemma ordinalMapVariation_bottomMerge {b c : ℕ} (g : Fin b →o Fin c)
    (hbc : c + 1 = b) (hg : ∀ i, (g i).val = i.val - 1) :
    ordinalMapVariation g = 1 := by
  have hs : Function.Surjective g := by
    intro j
    let i : Fin b := ⟨j.val + 1, by have h := j.isLt; omega⟩
    refine ⟨i, Fin.ext ?_⟩
    rw [hg]
    change j.val + 1 - 1 = j.val
    omega
  have hr := (ordinalImageCard_eq_target_iff g).mpr hs
  unfold ordinalMapVariation
  rw [hr]
  omega

/-- 概要：値1を欠く実像を底併合へ合成すると、変化量は1減る。
方針：合成の像の個数の保存と、終点の個数が一つ減る式を使う。
規約：自然数の切り捨ては像の個数の上限で検収する。使われ方：Riehl–Verity §4.2。 -/
lemma ordinalMapVariation_comp_bottomMerge_of_no_one {a b c : ℕ}
    (f : Fin a →o Fin b) (g : Fin b →o Fin c) (hbc : c + 1 = b)
    (hf : ∀ i, (f i).val ≠ 1) (hg : ∀ i, (g i).val = i.val - 1) :
    ordinalMapVariation (g.comp f) + 1 = ordinalMapVariation f := by
  have hr := ordinalImageCard_comp_bottomMerge_of_no_one f g hf hg
  have ha := ordinalImageCard_le_source (g.comp f)
  have hc := ordinalImageCard_le_target (g.comp f)
  unfold ordinalMapVariation
  omega

end SerrePositivity.InfinityCategories.HA.Monads
