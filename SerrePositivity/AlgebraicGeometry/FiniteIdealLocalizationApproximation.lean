module

public import Mathlib.RingTheory.Localization.Ideal
public import Mathlib.RingTheory.Finiteness.Ideal

/-!
概要：局所化先の有限個のイデアル切断を、元の有限生成部分イデアルに含める。
方針：有限個の分子を選び、その span を取る。
規約：元の環の Noether 性は要求しない。
使われ方：Stacks 01PF、有限型部分イデアルのアフィンでの供給。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
universe u v

/-- 局所化先の有限個のイデアル切断は、有限生成部分イデアルの像に含まれる。 -/
theorem exists_fg_subideal_localization_contains
    {A : Type u} [CommRing A] (M : Submonoid A)
    (B : Type v) [CommRing B] [Algebra A B] [IsLocalization M B]
    (I : Ideal A) (s : Finset B)
    (hs : ∀ x ∈ s, x ∈ I.map (algebraMap A B)) :
    ∃ J : Ideal A, J.FG ∧ J ≤ I ∧ ∀ x ∈ s, x ∈ J.map (algebraMap A B) := by
  classical
  have hx (x : s) : ∃ a : I × M,
      x.val * algebraMap A B a.2 = algebraMap A B a.1 :=
    (IsLocalization.mem_map_algebraMap_iff M B).mp (hs x.val x.property)
  choose a ha using hx
  let T : Finset A := Finset.univ.image (fun x : s ↦ ((a x).1 : A))
  let J := Ideal.span (T : Set A)
  have hJI : J ≤ I := Ideal.span_le.mpr (by
    intro b hb
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hb
    exact (a x).1.property)
  refine ⟨J, ⟨T, rfl⟩, hJI, ?_⟩
  intro x hxs
  let y : s := ⟨x, hxs⟩
  have hn : ((a y).1 : A) ∈ J := Ideal.subset_span
    (Finset.mem_image.mpr ⟨y, Finset.mem_univ _, rfl⟩)
  apply (IsLocalization.mem_map_algebraMap_iff M B).mpr
  exact ⟨⟨⟨(a y).1, hn⟩, (a y).2⟩, ha y⟩

end SerrePositivity.AlgebraicGeometry
