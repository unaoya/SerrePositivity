module

public import SerrePositivity.CommutativeAlgebra.RootTower.Basic
public import Mathlib.RingTheory.AdicCompletion.Algebra

/-! # 根の塔の p 進完備化

共通の根の塔を p 進完備化し、標準的な代数作用と拡大イデアルの比較を定義する。
正規化長さや perfectoid 性、Koszul ホモロジーの性質は使わない。
宣言名は既存利用先との互換性のため `SerrePositivity.Section2` に保持する。
-/

@[expose] public section
universe u
open IsLocalRing
namespace SerrePositivity.Section2

variable (A : Type u) [CommRing A] {h : ℕ} (t : Fin h → A) (p : ℕ)

/-- 標準的な根の塔の `p` 進完備化。 -/
abbrev CompletedTower :=
  AdicCompletion (Ideal.span {(p : Tower A t p)}) (Tower A t p)

/-- 基底環と塔の作用は、完備化への標準写像と両立する。 -/
instance : IsScalarTower A (Tower A t p) (CompletedTower A t p) :=
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

variable [IsLocalRing A]

/-- 完備化した塔における `m_A` の拡大。 -/
noncomputable def completedTowerMaxIdeal : Ideal (CompletedTower A t p) :=
  (maximalIdeal A).map (algebraMap A (CompletedTower A t p))

/-- 塔に拡大した極大イデアルを完備化へ移すと、直接の拡大と一致する。 -/
theorem towerMaxIdeal_map_completed :
    (towerMaxIdeal A t p).map (algebraMap (Tower A t p) (CompletedTower A t p)) =
      completedTowerMaxIdeal A t p := by
  simp only [towerMaxIdeal, completedTowerMaxIdeal, Ideal.map_map,
    ← IsScalarTower.algebraMap_eq]

end SerrePositivity.Section2
