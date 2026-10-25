module

public import SerrePositivity.InfinityCategories.F2.Presentable.SequentialNerveUniverse
public import SerrePositivity.InfinityCategories.F2.Presentable.SimplexTerminalFaceAnodyne
public import SerrePositivity.InfinityCategories.F2.Presentable.FiniteStageSourceCoslice

/-!
概要：偶数部分列の全有限始区間を偶数面と比較し、native な表示へ移す。
方針：全鎖の値と宇宙同型の部分列自然性を使う。
規約：全単体の射を厳密に比較する。
使われ方：全交互可算図式の偶数部分列と元の filtered 表示の全比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 概要：元の偶数自然数列は単調。
方針：自然数の線形算術。
規約：元の可算添字を使う。
使われ方：偶数部分列の全 nerve 関手。 -/
lemma alternatingEven_monotone : Monotone (fun n : ℕ ↦ 2 * n) := by
  intro n m h
  change 2 * n ≤ 2 * m
  omega

/-- 概要：偶数部分列への全始区間の制限は元の偶数面。
方針：全有限鎖の各値を計算する。
規約：全射の等式。
使われ方：交互図式の元の表示部分の検出。 -/
lemma sequentialNerveInitialSimplex_even (n : ℕ) :
    sequentialNerveInitialSimplex.{u} n ≫ nerveMap
      (sequentialSubsequenceFunctor.{u} (fun n ↦ 2 * n) alternatingEven_monotone) =
    SSet.stdSimplex.map (sequentialEvenFace n) ≫ sequentialNerveInitialSimplex (2 * n) := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro s
  exact ComposableArrows.ext (fun _ ↦ rfl) (fun _ _ ↦ Subsingleton.elim _ _)

/-- 概要：native な偶数部分列への始区間制限も同じ全偶数面。
方針：全宇宙同型を後合成して検出する。
規約：小さい元の nerve 写像の持ち上げを使う。
使われ方：native な可算表示の偶数部分列の比較。 -/
lemma nativeSequentialInitialSimplex_even (n : ℕ) :
    nativeSequentialInitialSimplex.{u} n ≫
      (SSet.uliftFunctor.{u + 1, u}).map (nerveMap
        (sequentialSubsequenceFunctor.{u} (fun n ↦ 2 * n) alternatingEven_monotone)) =
    SSet.stdSimplex.map (sequentialEvenFace n) ≫ nativeSequentialInitialSimplex (2 * n) := by
  apply (cancel_mono sequentialNerveUniverseIso.hom).mp
  rw [Category.assoc, sequentialNerveUniverseIso_subsequence,
    ← Category.assoc, nativeSequentialInitialSimplex_universe,
    Category.assoc, nativeSequentialInitialSimplex_universe]
  exact sequentialNerveInitialSimplex_even.{u + 1} n

/-- 概要：native な始区間における持ち上げた元の表示図式は finiteStageBaseMap そのもの。
方針：持ち上げ関手の合成保存を使う。
規約：元の小さい表示添字を保持する。
使われ方：全偶数部分列を元の表示前置図式へ戻す。 -/
lemma nativeSequentialInitialSimplex_liftedDiagram {I : SSet.{u}}
    (J : nerve (ULift.{u} ℕ) ⟶ I) (n : ℕ) :
    nativeSequentialInitialSimplex.{u} n ≫ (SSet.uliftFunctor.{u + 1, u}).map J =
      finiteStageBaseMap (sequentialNerveInitialSimplex n ≫ J) := by
  rw [nativeSequentialInitialSimplex, finiteStageBaseMap, Functor.map_comp, Category.assoc]

end SerrePositivity.InfinityCategories.F2.Presentable
