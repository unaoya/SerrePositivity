module

public import SerrePositivity.InfinityCategories.HA.Monads.OrdinalMapVariation

/-!
概要：有限単調射の順序和は実像の個数と変化量について加法的である。
方針：順序和の左右の実像を互いに交わらない有限集合として比較する。
規約：空の有限順序集合と実射の係数移送も含む。
使われ方：Riehl–Verity Proposition 4.2.15の実生成射の前置の幅、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）の前の最後の深さの実親の幅。
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.InfinityCategories.HA.Monads

/-- 概要：両端の個数と実有限単調射の異種等式は変化量を保つ。
方針：両端の個数と実射を同一視する。規約：明示的な個数の係数移送。
使われ方：Riehl–Verity §4.2の実順序和の表示の照合。 -/
lemma ordinalMapVariation_heq {a b c d : ℕ} (ha : a = c) (hb : b = d)
    (f : Fin a →o Fin b) (g : Fin c →o Fin d) (h : HEq f g) :
    ordinalMapVariation f = ordinalMapVariation g := by
  subst c
  subst d
  have he : f = g := eq_of_heq h
  subst g
  rfl

/-- 概要：実順序和の実像の個数は二つの実像の個数の和。
方針：二つの区間の包含へ像を分け、左右の実像が交わらないことを使う。
規約：空も含む二つの有限順序の実射。使われ方：Riehl–Verity §4.2の実前置の幅。 -/
lemma ordinalImageCard_append {m n p q : ℕ} (f : Fin m →o Fin n) (g : Fin p →o Fin q) :
    ordinalImageCard (ordinalAppend f g) = ordinalImageCard f + ordinalImageCard g := by
  have hu : (Finset.univ : Finset (Fin (m + p))) =
      Finset.univ.image (fun i : Fin m => i.castAdd p) ∪
        Finset.univ.image (fun j : Fin p => j.natAdd m) := by
    symm
    apply Finset.eq_univ_of_forall
    intro i
    refine Fin.addCases (fun i => ?_) (fun j => ?_) i
    · exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
    · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ j))
  have he : Finset.univ.image (ordinalAppend f g) =
      (Finset.univ.image f).image (fun i : Fin n => i.castAdd q) ∪
        (Finset.univ.image g).image (fun j : Fin q => j.natAdd n) := by
    rw [hu, Finset.image_union]
    simp only [Finset.image_image, Function.comp_def, ordinalAppend_castAdd, ordinalAppend_natAdd]
  have hd : Disjoint ((Finset.univ.image f).image (fun i : Fin n => i.castAdd q))
      ((Finset.univ.image g).image (fun j : Fin q => j.natAdd n)) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨y, _, hxy⟩ := Finset.mem_image.mp hj
    have hv := congrArg Fin.val hxy
    have hx := x.isLt
    change n + y.val = x.val at hv
    omega
  have hl : Function.Injective (fun i : Fin n => i.castAdd q) := by
    intro i j h
    apply Fin.ext
    exact congrArg (fun t : Fin (n + q) => t.val) h
  have hr : Function.Injective (fun j : Fin q => j.natAdd n) := by
    intro i j h
    apply Fin.ext
    have hv := congrArg Fin.val h
    change n + i.val = n + j.val at hv
    omega
  unfold ordinalImageCard
  rw [he, Finset.card_union_of_disjoint hd, Finset.card_image_of_injective _ hl,
    Finset.card_image_of_injective _ hr]

/-- 概要：実順序和の変化量は二つの変化量の和。
方針：実像の個数の加法性と両端の個数の和を比較する。
規約：空の有限順序も含む。使われ方：Riehl–Verity §4.2の実前置の幅の計算。 -/
lemma ordinalMapVariation_append {m n p q : ℕ} (f : Fin m →o Fin n) (g : Fin p →o Fin q) :
    ordinalMapVariation (ordinalAppend f g) = ordinalMapVariation f + ordinalMapVariation g := by
  have hf := ordinalImageCard_le_source f
  have hf' := ordinalImageCard_le_target f
  have hg := ordinalImageCard_le_source g
  have hg' := ordinalImageCard_le_target g
  unfold ordinalMapVariation
  rw [ordinalImageCard_append]
  omega

end SerrePositivity.InfinityCategories.HA.Monads
