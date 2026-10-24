module

public import SerrePositivity.InfinityCategories.F2.Ind.ConeTensorUniverseShapes
public import SerrePositivity.InfinityCategories.F2.Ind.TensorRightPointUniverse
public import SerrePositivity.InfinityCategories.F2.Ind.IndConeShapePoint

/-!
概要：元の余錐積の終点面は、元の宇宙比較で同じ大きい余錐積の全終点面へ移る。
方針：元の点固定・直積・余錐点の宇宙比較を合成する。
規約：元の試験族と同じ指定余錐点を厳密に保持する。
使われ方：小さい補間領域の相対余錐を、元の大きい全終点拡張へ戻す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
/-- 概要：元の余錐点の宇宙持ち上げは、同じ余錐形状比較で元の右包含になる。
方針：元の逆比較を相殺。規約：全点写像の等号。使われ方：元の全終点面の回収。 -/
lemma uliftCoconeShapeIso_tip_point (L : SSet.{u}) :
    ((HomotopyLimits.uliftStdSimplexIso.{u, u + 1} 0).inv ≫
      (SSet.uliftFunctor.{u + 1, u}).map (joinInr L (Δ[0] : SSet.{u}))) ≫
        (uliftCoconeShapeIso.{u, u + 1} L 0).hom =
    joinInr ((SSet.uliftFunctor.{u + 1, u}).obj L) Δ[0] := by
  rw [← indConeShape_inv_inr, Category.assoc, Iso.inv_hom_id, Category.comp_id]
/-- 概要：元の旧族側の終点面は、同じ宇宙比較で元の全終点面として回収される。
方針：元の点固定と余錐の宇宙比較。規約：全射の等号。使われ方：指定変換の旧族側。 -/
lemma coneTensorOldUniverseShape_target (A L : SSet.{u}) :
    (SSet.uliftFunctor.{u + 1, u}).map (tensorRightPoint A (joinInr L (Δ[0] : SSet.{u}))) ≫
      coneTensorOldUniverseShape A L =
    tensorRightPoint ((SSet.uliftFunctor.{u + 1, u}).obj A)
      (joinInr ((SSet.uliftFunctor.{u + 1, u}).obj L) Δ[0]) := by
  rw [coneTensorOldUniverseShape, ← Category.assoc, uliftTensorIso_hom_tensorRightPoint,
    tensorRightPoint_whiskerLeft, uliftCoconeShapeIso_tip_point]
/-- 概要：元の全終点面の余錐は、同じ宇宙比較で元の大きい余錐積の全終点面になる。
方針：元の両因子の宇宙比較と点固定の自然性。規約：全射の等号。使われ方：全拡張。 -/
lemma coneTensorUniverseShape_target (A L : SSet.{u}) :
    (SSet.uliftFunctor.{u + 1, u}).map
      (tensorRightPoint (join A (Δ[0] : SSet.{u})) (joinInr L Δ[0])) ≫
        coneTensorUniverseShape A L =
    (uliftCoconeShapeIso.{u, u + 1} A 0).hom ≫
      tensorRightPoint (join ((SSet.uliftFunctor.{u + 1, u}).obj A) Δ[0])
        (joinInr ((SSet.uliftFunctor.{u + 1, u}).obj L) Δ[0]) := by
  rw [coneTensorUniverseShape, ← Category.assoc, uliftTensorIso_hom_tensorRightPoint,
    ← Category.assoc, ← tensorRightPoint_naturality, Category.assoc,
    tensorRightPoint_whiskerLeft, uliftCoconeShapeIso_tip_point]
end SerrePositivity.InfinityCategories.F2.Ind
