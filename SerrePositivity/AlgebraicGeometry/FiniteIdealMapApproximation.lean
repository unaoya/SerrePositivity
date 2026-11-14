module

public import Mathlib.RingTheory.Finiteness.Ideal
public import Mathlib.RingTheory.Finiteness.Basic

/-!
概要：環準同型によるイデアルの像の有限個の元を、有限生成部分イデアルの像で捉える。
方針：生成イデアルの帰納法と有限個のイデアルの和を使う。
規約：局所化・全射性・Noether 性は仮定しない。
使われ方：Stacks 01PF、アフィン開上の有限個の切断を元の係数イデアルへ戻す。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
universe u v

/-- イデアルの像の有限個の元は、有限生成部分イデアルの像に同時に含まれる。 -/
theorem exists_fg_subideal_map_contains_finset
    {A : Type u} [CommRing A] {B : Type v} [CommRing B]
    (f : A →+* B) (I : Ideal A) (s : Finset B)
    (hs : ∀ x ∈ s, x ∈ I.map f) :
    ∃ J : Ideal A, J.FG ∧ J ≤ I ∧ ∀ x ∈ s, x ∈ J.map f := by
  classical
  have hsingle (y : B) (hy : y ∈ I.map f) :
      ∃ J : Ideal A, J.FG ∧ J ≤ I ∧ y ∈ J.map f := by
    change y ∈ Submodule.span B (f '' (I : Set A)) at hy
    induction hy using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨a, ha, rfl⟩ := hz
      refine ⟨Ideal.span {a}, ⟨{a}, by simp⟩, Ideal.span_le.mpr ?_, ?_⟩
      · simpa only [Set.singleton_subset_iff] using ha
      · exact Ideal.mem_map_of_mem f (Ideal.subset_span (Set.mem_singleton a))
    | zero => exact ⟨⊥, Submodule.fg_bot, bot_le, Ideal.zero_mem _⟩
    | add x y hx hy ihx ihy =>
      obtain ⟨J, hJ, hJI, hxJ⟩ := ihx
      obtain ⟨K, hK, hKI, hyK⟩ := ihy
      exact ⟨J ⊔ K, Submodule.FG.sup hJ hK, sup_le hJI hKI,
        Ideal.add_mem _ (Ideal.map_mono le_sup_left hxJ) (Ideal.map_mono le_sup_right hyK)⟩
    | smul a x hx ih =>
      obtain ⟨J, hJ, hJI, hxJ⟩ := ih
      exact ⟨J, hJ, hJI, Submodule.smul_mem _ a hxJ⟩
  revert hs
  induction s using Finset.induction_on with
  | empty =>
    intro hs
    exact ⟨⊥, Submodule.fg_bot, bot_le, by simp⟩
  | @insert b s hb ih =>
    intro hs
    obtain ⟨J, hJ, hJI, hbJ⟩ := hsingle b (hs b (by simp))
    obtain ⟨K, hK, hKI, hsK⟩ := ih (fun x hx ↦ hs x (Finset.mem_insert_of_mem hx))
    refine ⟨J ⊔ K, Submodule.FG.sup hJ hK, sup_le hJI hKI, ?_⟩
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact Ideal.map_mono le_sup_left hbJ
    · exact Ideal.map_mono le_sup_right (hsK x hx)

end SerrePositivity.AlgebraicGeometry
