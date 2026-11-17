module

public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionEpiAtomicity
public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionEpiWidth

/-!
概要：全実原子を、同じ実幅を持つ非退化な実原子と単体圏の実全射から回収する。
方針：元のnerveの宇宙持ち上げの非退化分解を取り、全射での実原子性と実幅の輸送を使う。
規約：非退化な元や全射の証人を入力にせず、元の単体から選ぶ。
使われ方：Riehl–Verity Proposition 4.2.15の退化した実原子因子の処理、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）の前の実filtrationの非退化生成元。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory
open scoped Simplicial

namespace SerrePositivity.InfinityCategories.HA.Monads

/-- 概要：任意の実原子は、同じ幅の非退化な実原子への実全射の作用として与えられる。
方針：元の単体集合の非退化分解を取り、原子性を反映し実幅を保存する。
規約：元の全関手と全射の実データ・元の次数以下の条件を保持。
使われ方：Riehl–Verity §4.2の実非退化原子への還元。 -/
lemma walkingAdjunctionAtomic_nondegenerate_core {n : ℕ} {X Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom X Y) n)
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨X⟩) (Y := ⟨Y⟩) H) :
    ∃ (m : ℕ) (f : ⦋n⦌ ⟶ ⦋m⦌) (_ : Epi f)
      (K : ComposableArrows (walkingAdjunctionHom X Y) m),
      WalkingAdjunctionLevelIsAtomic (X := ⟨X⟩) (Y := ⟨Y⟩) K ∧
      ULift.up K ∈ (WalkingAdjunctionHomShape.{u} X Y).nonDegenerate m ∧
      walkingAdjunctionOrdinalWidth K = walkingAdjunctionOrdinalWidth H ∧
      H = walkingAdjunctionSimplexFunctor f ⋙ K ∧ m ≤ n := by
  obtain ⟨m, f, hf, y, hy⟩ :=
    (WalkingAdjunctionHomShape.{u} X Y).exists_nonDegenerate (ULift.up H)
  have := hf
  let K := y.val.down
  have he : H = walkingAdjunctionSimplexFunctor f ⋙ K := congrArg ULift.down hy
  have hak : WalkingAdjunctionLevelIsAtomic (X := ⟨X⟩) (Y := ⟨Y⟩) K :=
    (walkingAdjunctionLevelIsAtomic_epi_iff f K).mp (by rw [← he]; exact ha)
  have hw := walkingAdjunctionOrdinalWidth_epi n m f K
  exact ⟨m, f, hf, K, hak, y.property,
    hw.symm.trans (congrArg walkingAdjunctionOrdinalWidth he).symm, he,
    SimplexCategory.le_of_epi f⟩

end SerrePositivity.InfinityCategories.HA.Monads
