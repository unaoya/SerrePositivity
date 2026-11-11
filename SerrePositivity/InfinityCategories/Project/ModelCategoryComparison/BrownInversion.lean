module

public import Mathlib.AlgebraicTopology.ModelCategory.BrownLemma
public import Mathlib.CategoryTheory.MorphismProperty.IsInvertedBy

/-!
# Brown 分解による任意の値圏への弱同値の反転

概要：Hovey §1.1・§5 の Brown 分解により、自明 fibration の反転を fibrant 対象の弱同値へ拡張する。
方針：弱同値を二つの自明 fibration と、その一方の切断を使って比較する。
規約：値圏には通常の圏構造だけを要求し、値圏のモデル構造は使わない。
使われ方：単体集合のモデル存在を仮定しない frame Hom の不変性。
-/

@[expose] public section

noncomputable section

universe u v u' v'

namespace SerrePositivity.InfinityCategories.Project.ModelCategoryComparison

open CategoryTheory HomotopicalAlgebra

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {D : Type u'} [Category.{v'} D]

/-- 概要：自明 fibration を反転する関手は fibrant 対象間の弱同値を反転する（Hovey §1.1）。
方針：Brown 分解の二つの自明 fibration の像と切断の像を同型にする。
規約：値圏の弱同値やモデル構造を仮定しない。
使われ方：anodyne 局所化を値に取る frame Hom に適用する。 -/
lemma map_isIso_of_fibrant (F : C ⥤ D) (hF : (trivialFibrations C).IsInvertedBy F)
    {X Y : C} [IsFibrant X] [IsFibrant Y] (f : X ⟶ Y) [WeakEquivalence f] :
    IsIso (F.map f) := by
  let h := Classical.choice (inferInstance : Nonempty (FibrantBrownFactorization f))
  have : Fibration h.p := (fibration_iff _).mpr h.hp
  have : IsIso (F.map h.p) := hF _ (mem_trivialFibrations _)
  have : IsIso (F.map h.r) := hF _ (mem_trivialFibrations _)
  have hr : F.map h.i ≫ F.map h.r = 𝟙 _ := by
    rw [← F.map_comp, h.i_r, F.map_id]
  have he : F.map h.i = inv (F.map h.r) := by
    apply (cancel_mono (F.map h.r)).mp
    simpa only [IsIso.inv_hom_id] using hr
  have : IsIso (F.map h.i) := by rw [he]; infer_instance
  rw [← h.fac, F.map_comp]
  infer_instance

end SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
