module

public import SerrePositivity.InfinityCategories.HA.Monads.OrdinalAppendVariation

/-!
概要：端点を共有する実単調射の貼り合わせの変化量は、左右の変化量の和。
方針：実像を左右の像へ分け、その交わりが共有する実一点であることを証明する。
規約：左の最大元と右の最小元の保存を明示する。
使われ方：Riehl–Verity Proposition 4.2.15の実水平合成の幅、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）の前の実原子分解の幅の法則。
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.InfinityCategories.HA.Monads

/-- 概要：端点共有の実貼り合わせの像の個数に1を加えると、左右の実像の個数の和。
方針：左右の実像の有限和と、交わりが実一点であることから計算する。
規約：実両端の保存を入力に明示。使われ方：Riehl–Verity §4.2の実水平合成の幅。 -/
lemma ordinalImageCard_glue {m n p q : ℕ} (f : Fin (m + 1) →o Fin (n + 1))
    (g : Fin (p + 1) →o Fin (q + 1)) (hf : f (Fin.last m) = Fin.last n) (hg : g 0 = 0) :
    ordinalImageCard (ordinalGlue f g) + 1 = ordinalImageCard f + ordinalImageCard g := by
  let l (i : Fin (n + 1)) : Fin (n + q + 1) := ⟨i.val, by have hi := i.isLt; omega⟩
  let r (j : Fin (q + 1)) : Fin (n + q + 1) := ⟨n + j.val, by have hj := j.isLt; omega⟩
  let S := (Finset.univ.image f).image l
  let T := (Finset.univ.image g).image r
  let z : Fin (n + q + 1) := ⟨n, by omega⟩
  have he : Finset.univ.image (ordinalGlue f g) = S ∪ T := by
    ext x
    constructor
    · intro hx
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
      by_cases hi : i.val ≤ m
      · let j : Fin (m + 1) := ⟨i.val, by omega⟩
        apply Finset.mem_union_left
        apply Finset.mem_image.mpr
        refine ⟨f j, Finset.mem_image_of_mem _ (Finset.mem_univ j), ?_⟩
        apply Fin.ext
        exact (ordinalGlue_val_left f g j).symm
      · let j : Fin (p + 1) := ⟨i.val - m, by have hp := i.isLt; omega⟩
        have hp : (⟨m + j.val, by have hj := j.isLt; omega⟩ : Fin (m + p + 1)) = i := by
          apply Fin.ext
          dsimp [j]
          omega
        have hv := ordinalGlue_val_right f g hf hg j
        rw [hp] at hv
        apply Finset.mem_union_right
        apply Finset.mem_image.mpr
        refine ⟨g j, Finset.mem_image_of_mem _ (Finset.mem_univ j), ?_⟩
        apply Fin.ext
        exact hv.symm
    · intro hx
      rcases Finset.mem_union.mp hx with hx | hx
      · obtain ⟨y, hy, he⟩ := Finset.mem_image.mp hx
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hy
        let j : Fin (m + p + 1) := ⟨i.val, by have hi := i.isLt; omega⟩
        apply Finset.mem_image.mpr
        refine ⟨j, Finset.mem_univ j, ?_⟩
        have hv : ordinalGlue f g j = l (f i) := Fin.ext (ordinalGlue_val_left f g i)
        exact hv.trans he
      · obtain ⟨y, hy, he⟩ := Finset.mem_image.mp hx
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hy
        let j : Fin (m + p + 1) := ⟨m + i.val, by have hi := i.isLt; omega⟩
        apply Finset.mem_image.mpr
        refine ⟨j, Finset.mem_univ j, ?_⟩
        have hv : ordinalGlue f g j = r (g i) := Fin.ext (ordinalGlue_val_right f g hf hg i)
        exact hv.trans he
  have hi : S ∩ T = {z} := by
    ext x
    constructor
    · intro hx
      obtain ⟨hxS, hxT⟩ := Finset.mem_inter.mp hx
      obtain ⟨i, _, hil⟩ := Finset.mem_image.mp hxS
      obtain ⟨j, _, hir⟩ := Finset.mem_image.mp hxT
      have hli := congrArg Fin.val hil
      have hrj := congrArg Fin.val hir
      change i.val = x.val at hli
      change n + j.val = x.val at hrj
      have hb := i.isLt
      apply Finset.mem_singleton.mpr
      apply Fin.ext
      change x.val = n
      omega
    · intro hx
      have hx' : x = z := Finset.mem_singleton.mp hx
      subst x
      apply Finset.mem_inter.mpr
      constructor
      · apply Finset.mem_image.mpr
        exact ⟨Fin.last n, Finset.mem_image.mpr ⟨Fin.last m, Finset.mem_univ _, hf⟩, rfl⟩
      · apply Finset.mem_image.mpr
        exact ⟨0, Finset.mem_image.mpr ⟨0, Finset.mem_univ _, hg⟩, rfl⟩
  have hl : Function.Injective l := by
    intro i j h
    apply Fin.ext
    exact congrArg (fun t : Fin (n + q + 1) => t.val) h
  have hr : Function.Injective r := by
    intro i j h
    apply Fin.ext
    have hv := congrArg Fin.val h
    change n + i.val = n + j.val at hv
    omega
  have hs : S.card = ordinalImageCard f := Finset.card_image_of_injective _ hl
  have ht : T.card = ordinalImageCard g := Finset.card_image_of_injective _ hr
  have hc := Finset.card_union_add_card_inter S T
  rw [← he, hi, Finset.card_singleton, hs, ht] at hc
  exact hc

/-- 概要：端点共有の実貼り合わせの変化量は左右の変化量の和。
方針：実像の個数と共有点の個数1の式を両端の個数の式へ適用する。
規約：元の実単調射の全貼り合わせ。使われ方：Riehl–Verity §4.2の実水平合成の幅。 -/
lemma ordinalMapVariation_glue {m n p q : ℕ} (f : Fin (m + 1) →o Fin (n + 1))
    (g : Fin (p + 1) →o Fin (q + 1)) (hf : f (Fin.last m) = Fin.last n) (hg : g 0 = 0) :
    ordinalMapVariation (ordinalGlue f g) = ordinalMapVariation f + ordinalMapVariation g := by
  have hi := ordinalImageCard_glue f g hf hg
  have hfs := ordinalImageCard_le_source f
  have hft := ordinalImageCard_le_target f
  have hgs := ordinalImageCard_le_source g
  have hgt := ordinalImageCard_le_target g
  unfold ordinalMapVariation
  omega

end SerrePositivity.InfinityCategories.HA.Monads
