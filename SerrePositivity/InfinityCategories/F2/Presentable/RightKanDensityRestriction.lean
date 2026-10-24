module

public import SerrePositivity.InfinityCategories.F2.Presentable.DensityConeOppositeRestriction
public import SerrePositivity.InfinityCategories.F1B.KanExtension.LocalCanonicalConeOpposite

/-!
概要：小さい左 Kan 比較添字の反転を標準右 Kan 錐へ接続する。
方針：標準局所錐の反転と添字制限の可換性を合わせる。
規約：元の全錐の射と零単体の正規化を保持する。
使われ方：反対前層圏の密度から右 Kan の普遍性への接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 概要：反転した局所添字への制限は元の標準左余錐の制限の反転に等しい。
方針：局所形状の反転同型と join の制限の自然性を合成する。
規約：任意の比較添字を許し、同値性や充填性を要求しない。
使われ方：元の小さい elements 図式による右 Kan 錐の計算。 -/
lemma rightKanCanonicalCone_op_restrict_val {A C J : SSet.{u}}
    (δ : A ⟶ C) (c : C _⦋0⦌) (f : J ⟶ leftKanShape δ c) :
    joinMap (𝟙 (Δ[0] : SSet.{u}))
        (SSet.opFunctor.map f ≫ (F1B.kanLeftKanShapeOpIso δ c).hom) ≫
      (rightKanCanonicalCone (SSet.opFunctor.map δ) (𝟙 C.op)
        (SSet.opObjEquiv.symm c)).val =
      (F1B.coconeReverseCone ((leftKanCanonicalCocone δ (𝟙 C) c).restrict f)).val := by
  have h := F1B.kanLeftKanCanonicalCocone_op_val δ (𝟙 C) c
  have h₀ : joinMap (𝟙 (Δ[0] : SSet.{u})) (F1B.kanLeftKanShapeOpIso δ c).hom ≫
      (rightKanCanonicalCone (SSet.opFunctor.map δ) (𝟙 C.op)
        (SSet.opObjEquiv.symm c)).val =
      (F1B.coconeReverseCone (leftKanCanonicalCocone δ (𝟙 C) c)).val := by
    rw [F1B.coconeReverseCone_val]
    exact h
  have hm : joinMap (𝟙 (Δ[0] : SSet.{u}))
      (SSet.opFunctor.map f ≫ (F1B.kanLeftKanShapeOpIso δ c).hom) =
      joinMap (𝟙 (Δ[0] : SSet.{u})) (SSet.opFunctor.map f) ≫
        joinMap (𝟙 (Δ[0] : SSet.{u})) (F1B.kanLeftKanShapeOpIso δ c).hom := by
    rw [← joinMap_comp, Category.id_comp]
  rw [hm, Category.assoc, h₀]
  exact coconeReverseCone_restrict_val _ f

end SerrePositivity.InfinityCategories.F2.Presentable
