module

public import SerrePositivity.InfinityCategories.F2.Ind.ConeTensorNativeExtendTarget
public import SerrePositivity.InfinityCategories.F2.Ind.ConeTensorUniverseBoundaries

/-!
概要：補間領域に元の全拡張を制限して余錐を作り直すと、元の両全境界が保たれる。
方針：補間領域への厳密な制限回収を、元の両 pushout 包含で制限する。
規約：元の全族と下方余錐を保持する。
使われ方：指定変換を加えた終点拡張の選び直し。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {A L : SSet.{u}} {X : SSet.{u + 1}}
  (E : join ((SSet.uliftFunctor.{u + 1, u}).obj A) Δ[0] ⊗
    join ((SSet.uliftFunctor.{u + 1, u}).obj L) Δ[0] ⟶ X)
  (c : JoinCocone ((SSet.uliftFunctor.{u + 1, u}).map (coneTensorCornerInclusion A L) ≫
    coneTensorUniverseShape A L ≫ E))
/-- 概要：選び直した全拡張は元の旧族全境界を保つ。
方針：元の左包含と宇宙比較で相殺。規約：全射の等号。使われ方：元の q の回収。 -/
lemma coneTensorNativeExtend_old :
    (joinInl ((SSet.uliftFunctor.{u + 1, u}).obj A) Δ[0] ▷
      join ((SSet.uliftFunctor.{u + 1, u}).obj L) Δ[0]) ≫
        (inv (coneTensorUniverseShape A L) ≫ coneTensorExtend c) =
    (joinInl ((SSet.uliftFunctor.{u + 1, u}).obj A) Δ[0] ▷
      join ((SSet.uliftFunctor.{u + 1, u}).obj L) Δ[0]) ≫ E := by
  apply (cancel_epi (coneTensorOldUniverseShape A L)).mp
  rw [← Category.assoc, ← coneTensorUniverseShape_old, Category.assoc,
    IsIso.hom_inv_id_assoc, ← coneTensorCornerInclusion_old,
    Functor.map_comp, Category.assoc, coneTensorExtend_inclusion,
    ← Category.assoc, ← Functor.map_comp, coneTensorCornerInclusion_old,
    ← Category.assoc, coneTensorUniverseShape_old, Category.assoc]
/-- 概要：選び直した全拡張は元の下方余錐全境界を保つ。
方針：元の右包含と宇宙比較で相殺。規約：全射の等号。使われ方：指定 G の回収。 -/
lemma coneTensorNativeExtend_lower :
    (join ((SSet.uliftFunctor.{u + 1, u}).obj A) Δ[0] ◁
      joinInl ((SSet.uliftFunctor.{u + 1, u}).obj L) Δ[0]) ≫
        (inv (coneTensorUniverseShape A L) ≫ coneTensorExtend c) =
    (join ((SSet.uliftFunctor.{u + 1, u}).obj A) Δ[0] ◁
      joinInl ((SSet.uliftFunctor.{u + 1, u}).obj L) Δ[0]) ≫ E := by
  apply (cancel_epi (coneTensorLowerUniverseShape A L)).mp
  rw [← Category.assoc, ← coneTensorUniverseShape_lower, Category.assoc,
    IsIso.hom_inv_id_assoc, ← coneTensorCornerInclusion_lower,
    Functor.map_comp, Category.assoc, coneTensorExtend_inclusion,
    ← Category.assoc, ← Functor.map_comp, coneTensorCornerInclusion_lower,
    ← Category.assoc, coneTensorUniverseShape_lower, Category.assoc]
end SerrePositivity.InfinityCategories.F2.Ind
