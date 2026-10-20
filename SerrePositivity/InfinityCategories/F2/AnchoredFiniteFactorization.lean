module

public import SerrePositivity.InfinityCategories.F2.FilteredLeftFibrationDetection

/-!
概要：連続 Kan 模型への有限な相対射を、元の境界を保って有限部分複体へ下ろす。
方針：境界を含む有限部分複体を選び、相対因子分解で後続段へ移す。
規約：境界射の単射性は要求しない。
使われ方：二つの相対因子分解を共通境界で貼り合わせる。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：有限な相対射の因子分解は元の境界と単位への制限を厳密に保つ。
方針：境界の有限な台を選び、単位の自然性と相対因子分解を使う。
規約：底や fibration は不要。使われ方：共通境界付きの同時検出。 -/
lemma continuousKanReplacement_anchored_finite_factorization {A K E : SSet.{u}}
    [A.Finite] [K.Finite] (i : A ⟶ K) (a : A ⟶ E)
    (f : K ⟶ continuousKanReplacement.obj E)
    (h : a ≫ continuousKanReplacementUnit.app E = i ≫ f) :
    ∃ k : FiniteSubcomplex E, ∃ a' : A ⟶ k.val,
      ∃ r : K ⟶ continuousKanReplacement.obj k.val,
        a' ≫ k.val.ι = a ∧
        i ≫ r = a' ≫ continuousKanReplacementUnit.app k.val ∧
        r ≫ continuousKanReplacement.map k.val.ι = f := by
  obtain ⟨j, a₀, ha₀⟩ := finiteSubcomplex_factorization a
  have hh : (a₀ ≫ continuousKanReplacementUnit.app j.val) ≫
      continuousKanReplacement.map j.val.ι = i ≫ f := by
    rw [Category.assoc, ← continuousKanReplacementUnit.naturality j.val.ι,
      CategoryTheory.Functor.id_map, ← Category.assoc, ha₀]
    exact h
  obtain ⟨k, v, r, hi, hr⟩ := finiteSubcomplex_relative_factorization_after_preserving_functor
    continuousKanReplacement E i j (a₀ ≫ continuousKanReplacementUnit.app j.val) f hh
  let v' := Subcomplex.homOfLE (leOfHom v)
  refine ⟨k, a₀ ≫ v', r, ?_, ?_, hr⟩
  · dsimp only [v']
    rw [Category.assoc, Subcomplex.homOfLE_ι, ha₀]
  · rw [hi, Category.assoc, ← continuousKanReplacementUnit.naturality]
    rfl

end SerrePositivity.InfinityCategories.F2
