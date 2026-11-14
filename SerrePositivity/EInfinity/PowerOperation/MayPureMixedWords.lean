module

public import SerrePositivity.EInfinity.PowerOperation.MayColoredValues
public import SerrePositivity.EInfinity.PowerOperation.MayWordAdjacent
public import SerrePositivity.EInfinity.PowerOperation.MayMixedWordOrbits
public import Mathlib.Tactic.Abel

/-!
# May の二項展開の純粋項と混合項

May, Proposition 2.3(ii) の Δ(a,b) の表示の前段。
元の二色語を、二つの定数語と混合語へ重複なく分ける。
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers

/-- 全ての入力が同じ色である既存の語。 -/
def mayWordPure : (n : ℕ) → Bool → BinaryTensorWord n
  | 0, _ => PUnit.unit
  | n + 1, c => mayWordCons n c (mayWordPure n c)

lemma mayWordPure_colors (n : ℕ) (c : Bool) :
    binaryTensorWordColors n (mayWordPure n c) = fun _ => c := by
  induction n with
  | zero => funext i; exact Fin.elim0 i
  | succ n ih =>
    rw [mayWordPure, mayWordCons_colors, ih]
    funext i
    exact Fin.cases rfl (fun _ => rfl) i

lemma mayWord_eq_pure_or_mixed (n : ℕ) (w : BinaryTensorWord n) :
    (∃ c : Bool, mayWordPure n c = w) ∨
      ∃ i j, binaryTensorWordColors n w i ≠ binaryTensorWordColors n w j := by
  classical
  by_cases h : ∃ i j, binaryTensorWordColors n w i ≠ binaryTensorWordColors n w j
  · exact Or.inr h
  · apply Or.inl
    cases n with
    | zero =>
      refine ⟨false, ?_⟩
      cases w
      rfl
    | succ n =>
      refine ⟨binaryTensorWordColors (n + 1) w 0, ?_⟩
      apply (binaryTensorWordColorsEquiv (n + 1)).injective
      change binaryTensorWordColors (n + 1) (mayWordPure (n + 1) _) =
        binaryTensorWordColors (n + 1) w
      rw [mayWordPure_colors]
      funext i
      by_contra hi
      exact h ⟨0, i, hi⟩

variable (p : ℕ) [NeZero p]

lemma mayWordPure_injective : Function.Injective (mayWordPure p) := by
  intro c d h
  have he := congrArg
    (fun w => binaryTensorWordColors p w ⟨0, NeZero.pos p⟩) h
  simpa only [mayWordPure_colors] using he

/-- 元の全入力語は、二つの純粋語と混合語の直和そのもの。 -/
def mayPureMixedWordEquiv : Bool ⊕ MayMixedWord p ≃ BinaryTensorWord p := by
  classical
  apply Equiv.ofBijective (Sum.elim (mayWordPure p) Subtype.val)
  constructor
  · intro x y hxy
    cases x with
    | inl c =>
      cases y with
      | inl d => exact congrArg Sum.inl (mayWordPure_injective p hxy)
      | inr w =>
        obtain ⟨i, j, hij⟩ := w.property
        change mayWordPure p c = w.val at hxy
        rw [← hxy, mayWordPure_colors] at hij
        exact (hij rfl).elim
    | inr w =>
      cases y with
      | inl c =>
        obtain ⟨i, j, hij⟩ := w.property
        change w.val = mayWordPure p c at hxy
        rw [hxy, mayWordPure_colors] at hij
        exact (hij rfl).elim
      | inr v => exact congrArg Sum.inr (Subtype.ext hxy)
  · intro w
    rcases mayWord_eq_pure_or_mixed p w with ⟨c, hc⟩ | hm
    · exact ⟨.inl c, hc⟩
    · exact ⟨.inr ⟨w, hm⟩, rfl⟩

/-- 二つの純粋語の同次値は、元の a,b の反復入力。 -/
lemma mayColoredValue_pure {k : Type u} [CommRing k] (K : Complex k) (q : ℤ)
    (a b : K.X q) (n : ℕ) (c : Bool) :
    mayColoredValue K q a b n (mayWordPure n c) =
      mayRepeatedValue K q (if c then b else a) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [mayWordPure]
    cases c <;> change (HomologicalComplex.ιTensorObj K (power K n) _ _ _ _)
      (_ ⊗ₜ[k] mayColoredValue K q a b n (mayWordPure n _)) = _
    all_goals rw [ih]; rfl

/-- 反復入力の二項展開から純粋な二項を除くと、全混合語の和になる。 -/
lemma mayColoredValue_mixed_sum {k : Type u} [CommRing k] (K : Complex k) (q : ℤ)
    (a b : K.X q) :
    mayRepeatedValue K q (a + b) p - mayRepeatedValue K q a p - mayRepeatedValue K q b p =
      ∑ w : MayMixedWord p, mayColoredValue K q a b p w.val := by
  have h := Equiv.sum_comp (mayPureMixedWordEquiv p) (fun w => mayColoredValue K q a b p w)
  rw [Fintype.sum_sum_type] at h
  change (∑ c : Bool, mayColoredValue K q a b p (mayWordPure p c)) +
    (∑ w : MayMixedWord p, mayColoredValue K q a b p w.val) =
      ∑ w : BinaryTensorWord p, mayColoredValue K q a b p w at h
  rw [mayColoredValue_sum] at h
  simp only [mayColoredValue_pure, Fintype.sum_bool] at h
  change mayRepeatedValue K q b p + mayRepeatedValue K q a p +
    (∑ w : MayMixedWord p, mayColoredValue K q a b p w.val) =
      mayRepeatedValue K q (a + b) p at h
  rw [← h]
  abel

end SerrePositivity.EInfinity.PowerOperation
