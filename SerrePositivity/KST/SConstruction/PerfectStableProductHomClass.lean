module
public import SerrePositivity.KST.SConstruction.PerfectStableInfinity
public import Mathlib.AlgebraicTopology.SimplicialSet.HoFunctorMonoidal

/-!
概要：Cat^perf の直積内の辺の類を、二つの元射影で検出する。
方針：既存のホモトピー圏の直積同値の忠実性で、元二射影の類を同時に読む。
規約：両端・元の二辺を保持。新しい局所化や Verdier 商の API は使わない。
使われ方：実右面の上下比較の対角を、両端成分を保って接続するための補助。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet InfinityCategories
  LocalizingInvariants
open scoped Simplicial
private lemma productHomClass {X Y : SSet.{u}}
    {x y : (X ⊗ Y) _⦋0⦌}
    (f g : SSet.Truncated.Edge (X := (truncation 2).obj (X ⊗ Y)) x y)
    (h₀ : SSet.Truncated.HomotopyCategory.homMk (f.map ((truncation 2).map (fst X Y))) =
      SSet.Truncated.HomotopyCategory.homMk (g.map ((truncation 2).map (fst X Y))))
    (h₁ : SSet.Truncated.HomotopyCategory.homMk (f.map ((truncation 2).map (snd X Y))) =
      SSet.Truncated.HomotopyCategory.homMk (g.map ((truncation 2).map (snd X Y)))) :
    SSet.Truncated.HomotopyCategory.homMk f = SSet.Truncated.HomotopyCategory.homMk g := by
  let E := SSet.Truncated.HomotopyCategory.BinaryProduct.equivalence
    ((truncation 2).obj X) ((truncation 2).obj Y)
  letI := E.faithful_functor
  apply E.functor.map_injective
  exact Prod.ext h₀ h₁

/-- 概要：Cat^perf 直積の二辺は元の両射影の類で一致を検出できる。
方針：既存の直積比較の忠実性に元の二射影を渡す。
規約：元の四端点と辺を保持。使われ方：対角比較の端点制限の同時検出。 -/
lemma perfectStableProduct_homMk_eq_of_projections
    {x y : (perfectStableInfinity.{u} ⊗ perfectStableInfinity.{u}) _⦋0⦌}
    (f g : SSet.Truncated.Edge
      (X := (truncation 2).obj (perfectStableInfinity.{u} ⊗ perfectStableInfinity.{u})) x y)
    (h₀ : SSet.Truncated.HomotopyCategory.homMk (f.map ((truncation 2).map
      (fst perfectStableInfinity.{u} perfectStableInfinity.{u}))) =
        SSet.Truncated.HomotopyCategory.homMk (g.map ((truncation 2).map
          (fst perfectStableInfinity.{u} perfectStableInfinity.{u}))))
    (h₁ : SSet.Truncated.HomotopyCategory.homMk (f.map ((truncation 2).map
      (snd perfectStableInfinity.{u} perfectStableInfinity.{u}))) =
        SSet.Truncated.HomotopyCategory.homMk (g.map ((truncation 2).map
          (snd perfectStableInfinity.{u} perfectStableInfinity.{u})))) :
    SSet.Truncated.HomotopyCategory.homMk f = SSet.Truncated.HomotopyCategory.homMk g := by
  exact productHomClass f g h₀ h₁
/-- 概要：安定圏の ∞ 圏の直積の二辺は元の両射影の類で一致を検出できる。
方針：既存の直積比較の忠実性に元の二射影を渡す。
規約：元の四端点と辺を保持。使われ方：対角比較の端点制限の同時検出。 -/
lemma stableInfinityProduct_homMk_eq_of_projections
    {x y : (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u} ⊗ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u}) _⦋0⦌}
    (f g : SSet.Truncated.Edge
      (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u} ⊗ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u})) x y)
    (h₀ : SSet.Truncated.HomotopyCategory.homMk (f.map ((truncation 2).map
      (fst _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u} _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u}))) =
        SSet.Truncated.HomotopyCategory.homMk (g.map ((truncation 2).map
          (fst _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u} _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u}))))
    (h₁ : SSet.Truncated.HomotopyCategory.homMk (f.map ((truncation 2).map
      (snd _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u} _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u}))) =
        SSet.Truncated.HomotopyCategory.homMk (g.map ((truncation 2).map
          (snd _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u} _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u})))) :
    SSet.Truncated.HomotopyCategory.homMk f = SSet.Truncated.HomotopyCategory.homMk g := by
  exact productHomClass f g h₀ h₁
end SerrePositivity.KST.SConstruction
