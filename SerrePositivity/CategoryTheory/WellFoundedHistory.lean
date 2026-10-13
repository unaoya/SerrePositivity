module

public import Mathlib.Order.WellFounded

/-! # 履歴を保つ整礎再帰

型の異なる初期部分を再帰の値にできる。延長の実構成とその制限一致は
呼出側で証明する必要があり、この補題はそれらから全段の一致を導く。
-/

public section
namespace SerrePositivity
universe u v

/-- 良い先行履歴をすべて保つ延長があれば、全段で両立する履歴を構成できる。
無効な先行履歴への既定値は再帰の全域化だけに使い、完成した族では使われない。 -/
theorem exists_coherent_wellFounded_history
    {ι : Type u} {r : ι → ι → Prop} (wf : WellFounded r)
    (H : ι → Type v) [∀ i, Nonempty (H i)]
    (restrict : ∀ j i, r j i → H i → H j)
    (P : ∀ i, H i → Prop)
    (extend : ∀ i (p : ∀ j, r j i → H j),
      (∀ j h, P j (p j h)) →
      (∀ j k (hj : r j i) (hk : r k i) (hjk : r j k),
        restrict j k hjk (p k hk) = p j hj) →
      ∃ x : H i, P i x ∧ ∀ j h, restrict j i h x = p j h) :
    ∃ s : ∀ i, H i, ∀ i, P i (s i) ∧ ∀ j h, restrict j i h (s i) = s j := by
  classical
  let good (i : ι) (p : ∀ j, r j i → H j) : Prop :=
    (∀ j h, P j (p j h)) ∧
    (∀ j k (hj : r j i) (hk : r k i) (hjk : r j k),
      restrict j k hjk (p k hk) = p j hj)
  let step (i : ι) (p : ∀ j, r j i → H j) : H i :=
    if h : good i p then Classical.choose (extend i p h.1 h.2) else Classical.choice inferInstance
  have step_spec (i : ι) (p : ∀ j, r j i → H j) (h : good i p) :
      P i (step i p) ∧ ∀ j hj, restrict j i hj (step i p) = p j hj := by
    dsimp only [step]
    rw [dite_eq_left h]
    exact Classical.choose_spec (extend i p h.1 h.2)
  let s : ∀ i, H i := wf.fix step
  refine ⟨s, ?_⟩
  intro i
  induction i using wf.induction with
  | h i ih =>
    have hp : good i (fun j _ ↦ s j) := by
      constructor
      · exact fun j hj ↦ (ih j hj).1
      · exact fun j k hj hk hjk ↦ (ih k hk).2 j hjk
    have hs : s i = step i (fun j _ ↦ s j) := WellFounded.fix_eq wf step i
    rw [hs]
    exact step_spec i (fun j _ ↦ s j) hp

end SerrePositivity
