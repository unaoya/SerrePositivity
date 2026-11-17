module

public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionDegeneracies
public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionOrdinalWidthDegeneracy

/-!
概要：任意の単体圏の実全射による再添字付けは有限順序の幅を保つ。
方針：始点次数に帰納し、非単射なら実退化を一つ外し、単射なら実恒等射へ戻す。
規約：一つの退化に限定せず、元の全実関手の作用を検収する。
使われ方：Riehl–Verity Proposition 4.2.15の退化因子から非退化な元への幅の輸送、
HA Proposition 4.7.3.3、Kerodon Remark 6.2.1.4（Tag 02EN）の前の実filtration。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory
open scoped Simplicial

namespace SerrePositivity.InfinityCategories.HA.Monads

/-- 概要：任意の実全射の単体作用は、元の全実鎖の有限順序の幅を保つ。
方針：全射の実恒等射または一つの実退化への分解を、始点次数で帰納する。
規約：単体圏の元のEpiを用いる。使われ方：Riehl–Verity §4.2の全実退化での幅の輸送。 -/
lemma walkingAdjunctionOrdinalWidth_epi {X Y : WalkingAdjunctionPoint} :
    ∀ (m n : ℕ) (f : ⦋m⦌ ⟶ ⦋n⦌) [Epi f]
      (H : ComposableArrows (walkingAdjunctionHom X Y) n),
      walkingAdjunctionOrdinalWidth (walkingAdjunctionSimplexFunctor f ⋙ H) =
        walkingAdjunctionOrdinalWidth H := by
  intro m
  induction m with
  | zero =>
    intro n f hf H
    have hn : n = 0 := by have h := SimplexCategory.le_of_epi f; omega
    subst n
    rw [SimplexCategory.eq_id_of_epi f, walkingAdjunctionSimplexFunctor_id, Functor.id_comp]
  | succ m ih =>
    intro n f hf H
    by_cases hfi : Function.Injective f.toOrderHom
    · have : Mono f := SimplexCategory.mono_iff_injective.mpr hfi
      have hn : m + 1 = n := le_antisymm (SimplexCategory.le_of_mono f)
        (SimplexCategory.le_of_epi f)
      subst n
      rw [SimplexCategory.eq_id_of_epi f, walkingAdjunctionSimplexFunctor_id, Functor.id_comp]
    · obtain ⟨i, g, he⟩ := SimplexCategory.eq_σ_comp_of_not_injective f hfi
      have hcomp : Epi (SimplexCategory.σ i ≫ g) := by rw [← he]; infer_instance
      have : Epi g := epi_of_epi (SimplexCategory.σ i) g
      rw [he, ← walkingAdjunctionSimplexFunctor_comp]
      change walkingAdjunctionOrdinalWidth ((nerve (walkingAdjunctionHom X Y)).σ i
        (walkingAdjunctionSimplexFunctor g ⋙ H)) = walkingAdjunctionOrdinalWidth H
      exact (walkingAdjunctionOrdinalWidth_degeneracy _ i).trans (ih n g H)

end SerrePositivity.InfinityCategories.HA.Monads
