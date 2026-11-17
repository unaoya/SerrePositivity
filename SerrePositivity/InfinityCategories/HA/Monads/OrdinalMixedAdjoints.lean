module

public import SerrePositivity.InfinityCategories.HA.Monads.OrdinalIntervalConcatenation

/-!
概要：既存の水平合成に使う有限Galois随伴と、端点共有の射を照合する。
方針：端点保存を実際に証明し、構成済みのGalois条件と随伴の一意性を使う。
規約：同じ射の照合であり、新しい随伴の存在を仮定しない。
使われ方：HA Proposition 4.7.3.3、Riehl–Verity Remark 3.3.8 の混合水平合成。
Kerodon Remark 6.2.1.4（Tag 02EN）。
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.InfinityCategories.HA.Monads

variable {m n p q : ℕ}

/-- 概要：非空の左因子が最小元を保てば、順序和も最小元を保つ。
方針：添字の輸送と左の点での値を計算する。
規約：右因子は空も許す。使われ方：Riehl–Verity Remark 3.3.8 の実右随伴の入力。 -/
lemma ordinalAppendNonempty_zero (f : Fin (m + 1) →o Fin (n + 1))
    (g : Fin p →o Fin q) (hf : f 0 = 0) : ordinalAppendNonempty f g 0 = 0 := by
  apply Fin.ext
  calc
    _ = (ordinalAppend f g ⟨0, by omega⟩).val := ordinalAppendNonempty_val f g 0
    _ = (f 0).val := ordinalAppend_val_left f g _ (by change 0 < m + 1; omega)
    _ = 0 := congrArg Fin.val hf

/-- 概要：非空の右因子が最大元を保てば、順序和も最大元を保つ。
方針：最後の点は右の区間にあることを使う。
規約：左因子は空も許す。使われ方：Riehl–Verity Remark 3.3.8 の実左随伴の入力。 -/
lemma ordinalAppend_last (f : Fin m →o Fin n)
    (g : Fin (p + 1) →o Fin (q + 1)) (hg : g (Fin.last p) = Fin.last q) :
    ordinalAppend (m := m) (n := n) (p := p + 1) (q := q + 1) f g (Fin.last (m + p)) =
      Fin.last (n + q) := by
  apply Fin.ext
  have hv := ordinalAppend_val_right f g (Fin.last (m + p)) (by change m ≤ m + p; omega)
  simp only [Fin.val_last, Nat.add_sub_cancel_left] at hv
  change (ordinalAppend f g (Fin.last (m + p))).val = n + (g (Fin.last p)).val at hv
  simpa only [hg, Fin.val_last] using hv

/-- 概要：順序和の実右随伴は最大元保存の射と区間表示の端点共有。
方針：構成済みのGalois条件と実右随伴の一意性を使う。
規約：端点の入力も上の法則から供給する。使われ方：Riehl–Verity Remark 3.3.8 の右作用。 -/
lemma ordinalRightAdjoint_append_glue (f : Fin (m + 1) →o Fin (n + 1))
    (hf : f (Fin.last m) = Fin.last n) (g : Fin q →o Fin p) :
    ordinalRightAdjoint (ordinalAppendNonempty (ordinalLeftAdjoint f hf) g)
        (ordinalAppendNonempty_zero _ _ (ordinalLeftAdjoint_zero f hf)) =
      ordinalGlue f (ordinalIntervalMap g) := by
  apply OrderHom.ext
  funext i
  exact (ordinalRightAdjoint_gc _ _).u_unique
    (ordinalGlue_interval_gc_right f hf g) (fun _ => rfl)

/-- 概要：順序和の実左随伴は区間表示と最小元保存の射の端点共有。
方針：既存の左随伴の一意性と構成済みのGalois条件を使う。
規約：左因子は空も許す。使われ方：Riehl–Verity Remark 3.3.8 の左作用。 -/
lemma ordinalLeftAdjoint_append_glue (f : Fin n →o Fin m)
    (g : Fin (p + 1) →o Fin (q + 1)) (hg : g 0 = 0) :
    ordinalLeftAdjoint
        (ordinalAppend (m := n) (n := m) (p := q + 1) (q := p + 1)
          f (ordinalRightAdjoint g hg))
        (ordinalAppend_last _ _ (ordinalRightAdjoint_last g hg)) =
      ordinalGlue (ordinalIntervalMap f) g := by
  apply OrderHom.ext
  funext i
  exact (ordinalLeftAdjoint_gc _ _).l_unique (ordinalGlue_interval_gc f g hg) (fun _ => rfl)

/-- 概要：逆順の混合合成に使う区間の回収は二つの射の端点共有。
方針：最大元付加の単射性で比較し、同じ右随伴の一意性を使う。
規約：区間の端点条件は元の混合合成の実射のもの。使われ方：Riehl–Verity Remark 3.3.8。 -/
lemma ordinalRecoverMap_append_glue (f : Fin (m + 1) →o Fin (n + 1))
    (g : Fin (p + 1) →o Fin (q + 1)) (hf : f (Fin.last m) = Fin.last n) (hg : g 0 = 0)
    (h₀ : ordinalAppendNonempty (ordinalLeftAdjoint f hf) (ordinalRightAdjoint g hg) 0 = 0)
    (h₁ : ordinalAppendNonempty (ordinalLeftAdjoint f hf) (ordinalRightAdjoint g hg)
      (Fin.last (n + q + 1)) = Fin.last (m + p + 1)) :
    ordinalRecoverMap
        (ordinalAppendNonempty (ordinalLeftAdjoint f hf) (ordinalRightAdjoint g hg)) h₀ h₁ =
      ordinalGlue f g := by
  apply ordinalAdjoinTop_injective
  rw [ordinalRecoverMap_adjoin]
  have hc := ordinalGlue_interval_gc_right f hf (ordinalRightAdjoint g hg)
  rw [ordinalIntervalMap_rightAdjoint, ordinalGlue_adjoinTop] at hc
  apply OrderHom.ext
  funext i
  exact (ordinalRightAdjoint_gc _ h₀).u_unique hc (fun _ => rfl)

end SerrePositivity.InfinityCategories.HA.Monads
