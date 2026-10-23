module

public import SerrePositivity.InfinityCategories.F2.CatInfinity.ConeHomotopyTetrahedra

/-!
概要：錐の始域の標準三角形の底辺と二脚。
方針：指定された単体の境界と既存の合成則を使う。
規約：辺と同型の値を新しく選択しない。
使われ方：全錐の比較円柱の三つの合成関係の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：錐の始域の標準三角形の底辺と二脚の指定単体への一致。
方針：標準三角形の面と円柱の側面の式を使う。
規約：元の二単体と一次単体を保つ。
使われ方：錐の四面の同型を各脚の指定比較同型に結び付ける。 -/
lemma coneDomainTriangle_zero {K : SSet.{u}} (k : K _⦋1⦌) :
    (join (Δ[0] : SSet.{u}) K).δ 0 (coneDomainTriangle k) =
      (joinInr Δ[0] K).app (Opposite.op ⦋1⦌) k := by
  rw [coneDomainTriangle, ← stdSimplex.yonedaEquiv_δ_comp,
    coneTriangleInclusion_zero, SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
/-- 概要：錐の始域の標準三角形の底辺と二脚の指定単体への一致。
方針：標準三角形の面と円柱の側面の式を使う。
規約：元の二単体と一次単体を保つ。
使われ方：錐の四面の同型を各脚の指定比較同型に結び付ける。 -/
lemma coneDomainTriangle_face {K : SSet.{u}} (k : K _⦋1⦌) (i : Fin 2) :
    (join (Δ[0] : SSet.{u}) K).δ i.succ (coneDomainTriangle k) =
      (coneDomainLeg (K.δ i k)).edge := by
  rw [coneDomainTriangle, ← stdSimplex.yonedaEquiv_δ_comp,
    coneTriangleInclusion_face, stdSimplex.δ_comp_yonedaEquiv_symm]
  rfl

end SerrePositivity.InfinityCategories.F2
