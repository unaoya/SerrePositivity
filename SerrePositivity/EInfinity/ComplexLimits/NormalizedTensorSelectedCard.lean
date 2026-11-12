module
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorSelectionCard

/-!
概要：選択 cochain を明示次数と濃度の等式で表示し、元の選択係数へ厳密に戻す。
方針：同じ列挙で選んだ全列の最上位普遍成分を、同じ最大点へ輸送する。
規約：元の実 cochain・最大点・次数を保つ。使われ方：像の列挙との同じ次数での比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open scoped Simplicial
variable (A : Type u) [CommRing A] (X Y : Complex A)

def normalizedTensorElementSelectedCochainAtMaxOfCard {n : ℕ}
    (c : ComposableArrows (normalizedTensorElementIndex A X Y) n)
    (J : Finset (Fin (n + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ))
    (r : ℕ) (hc : J.card = r + 1) :
    GradedHom A X ((normalizedTensorElementDiagram A X Y).obj (c.obj (J.max' hJ))) k :=
  cast (congrArg (fun i => (GradedHom A X
    ((normalizedTensorElementDiagram A X Y).obj (c.obj i)) k : Type u))
      (normalizedTensorElementSelectionOfCard_last J r hc hJ))
    ((normalizedTensorElementUniversalLinear A X Y
      ((SimplexCategory.toCat.map
        (normalizedTensorElementSelectionOfCard J r hc)).toFunctor ⋙ c)).val.component
        Finset.univ k Finset.univ_nonempty
        (by simpa only [Finset.card_univ, Fintype.card_fin, ← hc] using hk))

lemma normalizedTensorElementSelectedCochainAtMax_eq_ofCard {n : ℕ}
    (c : ComposableArrows (normalizedTensorElementIndex A X Y) n)
    (J : Finset (Fin (n + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)) :
    normalizedTensorElementSelectedCochainAtMax A X Y c J k hJ hk =
      normalizedTensorElementSelectedCochainAtMaxOfCard A X Y c J k hJ hk (J.card - 1)
        (by have := Finset.card_pos.mpr hJ; omega) := rfl

lemma normalizedTensorElementSelectedCochainAtMaxOfCard_congr {n : ℕ}
    (c : ComposableArrows (normalizedTensorElementIndex A X Y) n)
    (J : Finset (Fin (n + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ))
    (r s : ℕ) (hrs : r = s) (hr : J.card = r + 1) (hs : J.card = s + 1) :
    normalizedTensorElementSelectedCochainAtMaxOfCard A X Y c J k hJ hk r hr =
      normalizedTensorElementSelectedCochainAtMaxOfCard A X Y c J k hJ hk s hs := by
  subst s
  rfl

lemma normalizedTensorElementSelectedCochainAtMaxOfCard_raw {n : ℕ}
    (c : ComposableArrows (normalizedTensorElementIndex A X Y) n)
    (J : Finset (Fin (n + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ))
    (r : ℕ) (hc : J.card = r + 1) :
    HEq (normalizedTensorElementSelectedCochainAtMaxOfCard A X Y c J k hJ hk r hc)
      ((normalizedTensorElementUniversalLinear A X Y
        ((SimplexCategory.toCat.map
          (normalizedTensorElementSelectionOfCard J r hc)).toFunctor ⋙ c)).val.component
            Finset.univ k Finset.univ_nonempty
            (by simpa only [Finset.card_univ, Fintype.card_fin, ← hc] using hk)) := by
  exact cast_heq _ _

end SerrePositivity.EInfinity.ComplexLimits
