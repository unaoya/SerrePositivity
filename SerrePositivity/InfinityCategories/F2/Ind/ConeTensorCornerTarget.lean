module

public import SerrePositivity.InfinityCategories.F2.Ind.ConeTensorNativeExtendBoundary

/-!
概要：元の補間領域に制限した全拡張の指定部分は、同じ全終点面の元の旧族。
方針：補間領域の指定包含と全宇宙比較の終点面を照合する。
規約：元の試験族と同じ余錐点を保持する。
使われ方：scalar comma の相対余錐へ渡す全境界の厳密な可換性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
/-- 概要：元の全拡張の補間領域上の指定部分は同じ終点面の旧族制限。
方針：元の包含と宇宙比較の等号。規約：全射の等号。使われ方：指定変換の貼り付け。 -/
lemma coneTensorCorner_target {A L : SSet.{u}} {X : SSet.{u + 1}}
    (E : join ((SSet.uliftFunctor.{u + 1, u}).obj A) Δ[0] ⊗
      join ((SSet.uliftFunctor.{u + 1, u}).obj L) Δ[0] ⟶ X) :
    (SSet.uliftFunctor.{u + 1, u}).map (coneTensorTargetInclusion A L) ≫
      ((SSet.uliftFunctor.{u + 1, u}).map (coneTensorCornerInclusion A L) ≫
        coneTensorUniverseShape A L ≫ E) =
    joinInl ((SSet.uliftFunctor.{u + 1, u}).obj A) Δ[0] ≫
      tensorRightPoint (join ((SSet.uliftFunctor.{u + 1, u}).obj A) Δ[0])
        (joinInr ((SSet.uliftFunctor.{u + 1, u}).obj L) Δ[0]) ≫ E := by
  rw [← Category.assoc, ← Functor.map_comp, coneTensorTargetInclusion_comp,
    Functor.map_comp]
  have h := congrArg (fun f ↦
    (SSet.uliftFunctor.{u + 1, u}).map (joinInl A (Δ[0] : SSet.{u})) ≫ f ≫ E)
    (coneTensorUniverseShape_target A L)
  simpa only [Category.assoc, ← uliftCoconeShapeIso_inl] using h
end SerrePositivity.InfinityCategories.F2.Ind
