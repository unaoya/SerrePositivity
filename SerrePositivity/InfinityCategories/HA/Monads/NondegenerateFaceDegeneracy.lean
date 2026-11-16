module

public import Mathlib.AlgebraicTopology.SimplicialSet.Degenerate

/-!
概要：非退化な面を持つ単体の退化は、その面の両隣の位置にしか現れない。
方針：面と退化の合成が非退化単体を表示するため単射となることを使う。
規約：任意の単体集合の元の面と退化について証明する。
使われ方：Riehl–Verity §4.1–§4.2の実親の非退化性、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）の前のcoherentな随伴の実構成。
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace SerrePositivity.InfinityCategories.HA.Monads

/-- 概要：非退化な面の上の退化は隣接位置にあり、その低次の単体は同じ面。
方針：面と退化の合成の単射性と有限全順序の自己単射の恒等性を使う。
規約：退化の低次の単体を別の仮定で指定しない。使われ方：Riehl–Verity §4.1の実親。 -/
lemma degeneracy_over_nondegenerate_face {X : SSet.{u}} {n : ℕ}
    (z : X _⦋n + 2⦌) (k : Fin (n + 3)) (j : Fin (n + 2)) (t : X _⦋n + 1⦌)
    (hdeg : X.σ j t = z) (hnd : X.δ k z ∈ X.nonDegenerate (n + 1)) :
    (k = j.castSucc ∨ k = j.succ) ∧ X.σ j (X.δ k z) = z := by
  let f : ⦋n + 1⦌ ⟶ ⦋n + 1⦌ := SimplexCategory.δ k ≫ SimplexCategory.σ j
  have he : X.map f.op t = X.δ k z := by
    calc
      X.map f.op t = X.δ k (X.σ j t) := by
        change X.map ((SimplexCategory.σ j).op ≫ (SimplexCategory.δ k).op) t = _
        rw [X.map_comp]
        rfl
      _ = _ := congrArg (fun a => X.δ k a) hdeg
  have : Mono f := X.mono_of_nonDegenerate ⟨_, hnd⟩ f t he
  have hf : f = 𝟙 _ := SimplexCategory.eq_id_of_mono f
  have ht : t = X.δ k z := by simpa [hf] using he
  refine ⟨?_, by rw [← ht]; exact hdeg⟩
  by_cases hleft : k = j.castSucc
  · exact Or.inl hleft
  · right
    by_contra hright
    have ha : j.castSucc ∈ Set.range k.succAbove := by
      rw [Fin.range_succAbove]
      exact Ne.symm hleft
    have hb : j.succ ∈ Set.range k.succAbove := by
      rw [Fin.range_succAbove]
      exact Ne.symm hright
    obtain ⟨a, ha⟩ := ha
    obtain ⟨b, hb⟩ := hb
    have hab : a = b := (SimplexCategory.mono_iff_injective.mp (inferInstance : Mono f)) (by
      change j.predAbove (k.succAbove a) = j.predAbove (k.succAbove b)
      rw [ha, hb, Fin.predAbove_castSucc_self, Fin.predAbove_succ_self])
    have hc : j.castSucc = j.succ := ha.symm.trans ((congrArg k.succAbove hab).trans hb)
    have hv := congrArg Fin.val hc
    change j.val = j.val + 1 at hv
    omega

/-- 概要：非退化な面を持ち両隣の退化に一致しない単体は非退化。
方針：退化なら実退化の像として表し、隣接位置への限定を適用する。
規約：元の単体集合の非退化性を結論にする。使われ方：Riehl–Verity §4.1の実親の検収。 -/
lemma nondegenerate_of_face_and_no_adjacent_degeneracy {X : SSet.{u}} {n : ℕ}
    (z : X _⦋n + 2⦌) (k : Fin (n + 3))
    (hnd : X.δ k z ∈ X.nonDegenerate (n + 1))
    (hno : ∀ j : Fin (n + 2), (k = j.castSucc ∨ k = j.succ) → X.σ j (X.δ k z) ≠ z) :
    z ∈ X.nonDegenerate (n + 2) := by
  apply (SSet.mem_nonDegenerate_iff_notMem_degenerate _ _).mpr
  intro hd
  rw [SSet.degenerate_eq_iUnion_range_σ] at hd
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hd
  obtain ⟨t, ht⟩ := hj
  obtain ⟨hpos, he⟩ := degeneracy_over_nondegenerate_face z k j t ht hnd
  exact hno j hpos he

end SerrePositivity.InfinityCategories.HA.Monads
