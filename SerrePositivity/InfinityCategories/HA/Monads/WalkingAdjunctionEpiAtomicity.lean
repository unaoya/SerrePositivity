module

public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionDegeneracies
public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionAtomicEndpoints

/-!
概要：任意の単体圏の実全射は端点を保ち、再添字付けによる実原子性の同値を与える。
方針：両端の実原像を選び、実単調性と端点による実原子性の判定を使う。
規約：切断を追加の入力に置かず、元の全射性から直接回収する。
使われ方：Riehl–Verity Proposition 4.2.15の非退化な実原子への輸送、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）の前の実filtrationの退化因子。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory
open scoped Simplicial

namespace SerrePositivity.InfinityCategories.HA.Monads

/-- 概要：単体圏の実全射の有限順序関手は最初と最後の実頂点を保つ。
方針：最小元と最大元の実原像を選び、その上下で実単調性を使う。
規約：次数0も含む。使われ方：Riehl–Verity §4.2の実原子性の端点条件の輸送。 -/
lemma walkingAdjunctionSimplexFunctor_epi_endpoints {m n : ℕ} (f : ⦋m⦌ ⟶ ⦋n⦌) [Epi f] :
    (walkingAdjunctionSimplexFunctor f).obj 0 = 0 ∧
      (walkingAdjunctionSimplexFunctor f).obj (Fin.last m) = Fin.last n := by
  have hs := SimplexCategory.epi_iff_surjective.mp (inferInstance : Epi f)
  constructor
  · obtain ⟨i, hi⟩ := hs 0
    apply le_antisymm ?_ (Fin.zero_le _)
    have h := f.toOrderHom.monotone (Fin.zero_le i)
    change f.toOrderHom 0 ≤ 0
    rw [hi] at h
    exact h
  · obtain ⟨i, hi⟩ := hs (Fin.last n)
    apply le_antisymm (Fin.le_last _) ?_
    have h := f.toOrderHom.monotone (Fin.le_last i)
    change Fin.last n ≤ f.toOrderHom (Fin.last m)
    rw [hi] at h
    exact h

/-- 概要：任意の実単体全射による再添字付けで、元の全実鎖の原子性は同値となる。
方針：実最初・最後の頂点の保存を、端点による原子性の必要十分条件へ適用する。
規約：全四Hom、全次数。使われ方：Riehl–Verity §4.2の非退化な実原子の回収。 -/
lemma walkingAdjunctionLevelIsAtomic_epi_iff {m n : ℕ} {X Y : WalkingAdjunctionPoint}
    (f : ⦋m⦌ ⟶ ⦋n⦌) [Epi f] (H : ComposableArrows (walkingAdjunctionHom X Y) n) :
    WalkingAdjunctionLevelIsAtomic (X := ⟨X⟩) (Y := ⟨Y⟩)
      (walkingAdjunctionSimplexFunctor f ⋙ H) ↔
    WalkingAdjunctionLevelIsAtomic (X := ⟨X⟩) (Y := ⟨Y⟩) H := by
  obtain ⟨h0, hl⟩ := walkingAdjunctionSimplexFunctor_epi_endpoints f
  rw [walkingAdjunctionLevelIsAtomic_iff_endpoint_cards,
    walkingAdjunctionLevelIsAtomic_iff_endpoint_cards]
  simp only [Functor.comp_obj, h0, hl]

end SerrePositivity.InfinityCategories.HA.Monads
