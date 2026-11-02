module

public import SerrePositivity.InfinityCategories.F1B.Joins.JoinShiftPrism
public import SerrePositivity.InfinityCategories.Core.JoinAssociatorRightPair

/-!
概要：二つの終端点を一つに潰す錐の射と境界の計算。
方針：join の結合同型で二つの点を隣接させ、標準零単体の終対象性で潰す。
規約：錐の底の単体集合は任意。
使われ方：普遍余錐の底をその頂点へ動かす円柱の構成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：二重に点を付加した錐の二つの点を一つへ潰す。
方針：二つの点の join から標準零単体への唯一の射を使う。
規約：底 A は保つ。
使われ方：錐を頂点へ縮める円柱の終域の正規化。 -/
def coneCollapse (A : SSet.{u}) :
    join (join A (Δ[0] : SSet.{u})) Δ[0] ⟶ join A Δ[0] :=
  (stableJoinAssociator A Δ[0] Δ[0]).hom ≫
    joinMap (𝟙 A) (SSet.const (stdSimplex.obj₀Equiv.symm 0))

/-- 概要：元の錐を最初の二因子へ入れて潰すと元の錐を回収する。
方針：結合同型の左境界と零単体の終対象性。
規約：二つの点のどちらも同じ点へ写す。
使われ方：円柱の左因子での境界。 -/
lemma coneCollapse_left (A : SSet.{u}) :
    joinInl (join A (Δ[0] : SSet.{u})) Δ[0] ≫ coneCollapse A = 𝟙 _ := by
  rw [coneCollapse, ← Category.assoc, stableJoinAssociator_inl, ← joinMap_comp,
    Category.id_comp]
  have h : joinInl (Δ[0] : SSet.{u}) Δ[0] ≫ SSet.const (stdSimplex.obj₀Equiv.symm 0) =
      𝟙 (Δ[0] : SSet.{u}) := stdSimplex.isTerminalObj₀.hom_ext _ _
  rw [h, joinMap_id]

/-- 概要：第一・第三因子の錐を潰しても元の錐を回収する。
方針：結合同型の中間因子の境界と零単体の終対象性。
規約：中間の点は使わない。
使われ方：錐の収縮の時間零での計算。 -/
lemma coneCollapse_middle (A : SSet.{u}) :
    joinMap (joinInl A (Δ[0] : SSet.{u})) (𝟙 (Δ[0] : SSet.{u})) ≫
      coneCollapse A = 𝟙 _ := by
  rw [coneCollapse, ← Category.assoc, stableJoinAssociator_middle, ← joinMap_comp,
    Category.id_comp]
  have h : joinInr (Δ[0] : SSet.{u}) Δ[0] ≫ SSet.const (stdSimplex.obj₀Equiv.symm 0) =
      𝟙 (Δ[0] : SSet.{u}) := stdSimplex.isTerminalObj₀.hom_ext _ _
  rw [h, joinMap_id]

/-- 概要：二つの点だけを入れた部分は一つの終端点へ潰れる。
方針：結合同型の後二因子の境界を使う。
規約：二点の join のパラメータ全体を忘れる。
使われ方：錐の収縮の時間一での計算。 -/
lemma coneCollapse_rightPair (A : SSet.{u}) :
    joinMap (joinInr A (Δ[0] : SSet.{u})) (𝟙 (Δ[0] : SSet.{u})) ≫ coneCollapse A =
      SSet.const (stdSimplex.obj₀Equiv.symm 0) ≫ joinInr A Δ[0] := by
  rw [coneCollapse, ← Category.assoc, stableJoinAssociator_rightPair, joinInr_joinMap]

/-- 概要：最後の点は潰した錐の頂点になる。
方針：結合同型の右端境界と零単体の終対象性。
規約：頂点の射を厳密に保つ。
使われ方：円柱の頂点を固定する条件。 -/
lemma coneCollapse_right (A : SSet.{u}) :
    joinInr (join A (Δ[0] : SSet.{u})) Δ[0] ≫ coneCollapse A = joinInr A Δ[0] := by
  rw [coneCollapse, ← Category.assoc, stableJoinAssociator_inr, Category.assoc,
    joinInr_joinMap, ← Category.assoc]
  have h : joinInr (Δ[0] : SSet.{u}) Δ[0] ≫ SSet.const (stdSimplex.obj₀Equiv.symm 0) =
      𝟙 (Δ[0] : SSet.{u}) := stdSimplex.isTerminalObj₀.hom_ext _ _
  rw [h, Category.id_comp]

end SerrePositivity.InfinityCategories.F1B
