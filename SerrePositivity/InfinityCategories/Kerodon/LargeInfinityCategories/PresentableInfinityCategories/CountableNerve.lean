module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.CountableFiniteExhaustion
public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
public import Mathlib.CategoryTheory.Countable

/-!
概要：可算圏の nerve の全単体が可算であることを示す。
方針：有限圏からの関手を対象・射の有限個のデータへ埋め込む。
規約：可算性のみを公開し、nerve に有限性を仮定しない。
使われ方：幾何学的実現の形状の有限部分複体による増大列。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：有限圏から可算圏への関手の型は可算。
方針：対象写像と全射写像の有限個の値へ関手を埋め込む。
規約：関手の公理は証明の一意性で除く。使われ方：nerve の各次数の可算性。 -/
lemma countable_functors_from_finite (A : Type v) [SmallCategory A]
    [Finite A] [∀ a b : A, Finite (a ⟶ b)]
    (C : Type u) [SmallCategory C] [CountableCategory C] : Countable (A ⥤ C) := by
  let code (F : A ⥤ C) : Σ o : A → C, ∀ a b : A, (a ⟶ b) → (o a ⟶ o b) :=
    ⟨F.obj, fun _ _ f ↦ F.map f⟩
  apply Function.Injective.countable (f := code)
  rintro ⟨fo, fm, fi, fc⟩ ⟨go, gm, gi, gc⟩ h
  dsimp [code] at h
  obtain ⟨rfl, hm⟩ := Sigma.mk.inj_iff.mp h
  have hm' : @fm = @gm := by
    funext a b f
    exact congrFun (congrFun (congrFun (eq_of_heq hm) a) b) f
  cases hm'
  rfl

/-- 概要：可算圏の nerve の全単体は可算。
方針：各次数を有限順序圏からの関手として数え、次数の可算直和を取る。
規約：射と対象を同じ宇宙に置く。使われ方：可算な添字形状の有限増大列。 -/
lemma countable_nerve_simplices (C : Type u) [SmallCategory C] [CountableCategory C] :
    Countable (nerve C).S := by
  have (n : ℕ) : Countable ((nerve C).obj (Opposite.op ⦋n⦌)) :=
    countable_functors_from_finite (Fin (n + 1)) C
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.countable_simplices_of_countable_levels (nerve C)

/-- 概要：単体圏は可算圏。
方針：対象を次数で数え、各射集合の有限性を使う。
規約：既存の圏構造を使う。使われ方：幾何学的実現の添字の可算性。 -/
lemma countableCategory_simplexCategory : CountableCategory SimplexCategory := by
  have : Countable SimplexCategory := Function.Injective.countable
    (f := SimplexCategory.len) (fun _ _ h ↦ SimplexCategory.ext h)
  exact ⟨inferInstance, fun _ _ ↦ inferInstance⟩

/-- 概要：元の幾何学的実現の添字形状は可算個の単体を持つ。
方針：単体圏の反対と宇宙変更が可算性を保つことを使う。
規約：既存の実現版の添字と同じ ULiftHom・ULift を使う。
使われ方：有限段階と可算列から実現の余極限を得る入口。 -/
lemma countable_geometricRealizationShape_simplices :
    Countable (nerve (ULiftHom.{u} (ULift.{u} SimplexCategoryᵒᵖ))).S := by
  let := countableCategory_simplexCategory
  exact countable_nerve_simplices _

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
