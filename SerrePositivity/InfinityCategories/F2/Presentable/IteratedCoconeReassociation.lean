module

public import SerrePositivity.InfinityCategories.Core.JoinAssociatorBoundary
public import SerrePositivity.InfinityCategories.Core.JoinAssociatorMiddle
public import SerrePositivity.InfinityCategories.Core.InitialUniqueness

/-!
概要：二重余錐の join を、一つの辺を右因子とする join に組み替える。
方針：join の結合同型と二点の join の標準辺表示を合成する。
規約：三つの部分形状への制限を全射の等式で保持する。
使われ方：余極限余錐から元の対象上の余錐を構成する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 概要：二重余錐の二つの右頂点を標準辺にまとめる射。
方針：結合同型の後で右因子を標準辺へ写す。
規約：元の左因子 K を保つ。
使われ方：slice 内の余錐の全体表示。 -/
def iteratedCoconeReassociation (K : SSet.{u}) :
    join (join K Δ[0]) Δ[0] ⟶ join K Δ[1] :=
  (stableJoinAssociator K Δ[0] Δ[0]).hom ≫ joinMap (𝟙 K) (joinStdSimplexIso 0 0).hom

/-- 概要：最初の余錐は右辺の始点への制限に写る。
方針：結合同型の左包含則を使う。
規約：全余錐上の等式。
使われ方：構成した slice 余錐の射影を元の余極限余錐へ固定する。 -/
lemma iteratedCoconeReassociation_inl (K : SSet.{u}) :
    joinInl (join K Δ[0]) Δ[0] ≫ iteratedCoconeReassociation K =
      joinMap (𝟙 K) (SSet.stdSimplex.δ (1 : Fin 2)) := by
  rw [iteratedCoconeReassociation, ← Category.assoc, stableJoinAssociator_inl,
    ← joinMap_comp, Category.id_comp, joinStdSimplexIso_zero_inl]

/-- 概要：中間の頂点を除く元の余錐は右辺の終点への制限に写る。
方針：結合同型の中間包含則を使う。
規約：元の対象への全余錐を厳密に回収する。
使われ方：slice 余錐の元の図式への制限。 -/
lemma iteratedCoconeReassociation_middle (K : SSet.{u}) :
    joinMap (joinInl K Δ[0]) (𝟙 (Δ[0] : SSet.{u})) ≫ iteratedCoconeReassociation K =
      joinMap (𝟙 K) (SSet.stdSimplex.δ (0 : Fin 2)) := by
  rw [iteratedCoconeReassociation, ← Category.assoc, stableJoinAssociator_middle,
    ← joinMap_comp, Category.id_comp, joinStdSimplexIso_zero_inr]

/-- 概要：最後の頂点は右辺の終点に写る。
方針：結合同型の右包含則と join の自然性を使う。
規約：元の対象の点射を固定する。
使われ方：slice へ curry する際の固定条件。 -/
lemma iteratedCoconeReassociation_inr (K : SSet.{u}) :
    joinInr (join K Δ[0]) Δ[0] ≫ iteratedCoconeReassociation K =
      SSet.stdSimplex.δ (0 : Fin 2) ≫ joinInr K Δ[1] := by
  rw [iteratedCoconeReassociation, ← Category.assoc, stableJoinAssociator_inr,
    Category.assoc, joinInr_joinMap, ← Category.assoc, joinStdSimplexIso_zero_inr]

end SerrePositivity.InfinityCategories.F2.Presentable
