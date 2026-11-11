module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.ExInfinityStages
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.ExDoubleHornFiller
public import Mathlib.AlgebraicTopology.SimplicialSet.KanComplex
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Ex∞ の Kan 性

概要：実際に構成した Ex∞ は全ての単体集合を Kan 複体へ送る。
方針：有限な horn の写像を有限反復へ因子化し、二回の Ex の後の具体的な充填を余極限へ送る。
規約：Moss 2020 Proposition 21。二重細分の充填候補と境界条件は本レーンで証明する。
使われ方：有限極限を保ち単位が anodyne である Kan 置換。

対応節は Kerodon 3.3（Tag 00XF）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
open CategoryTheory Limits
open scoped _root_.Simplicial

/--
概要：Ex∞ への正次元の horn の写像は標準単体へ延長できる。
方針：有限段階への因子化、二回の Ex の充填、余錐の遷移との整合を順に使う。
規約：Moss 2020 Proposition 21 の horn の充填の形。
使われ方：Ex∞ の Kan 性のインスタンス。
-/
theorem exInfinity_hornFilling (X : SSet.{u}) (n : ℕ) (hn : 0 < n) (k : Fin (n + 1))
    (f : (SSet.horn n k : SSet.{u}) ⟶ exInfinity.obj X) :
    ∃ g : Δ[n] ⟶ exInfinity.obj X, (SSet.horn n k).ι ≫ g = f := by
  obtain ⟨m, p, hp⟩ := exInfinity_finite_factorization (SSet.horn n k) X f
  refine ⟨exDoubleHornFiller ((exIterate m).obj X) n hn k p ≫
    (exInfinityStage (m + 2)).app X, ?_⟩
  rw [exDoubleHornFiller_boundary_assoc]
  have hnext : exUnitAt (SSet.ex.obj ((exIterate m).obj X)) ≫
      (exInfinityStage (m + 2)).app X = (exInfinityStage (m + 1)).app X :=
    exInfinityStage_succ X (m + 1)
  calc
    _ = p ≫ exUnitAt ((exIterate m).obj X) ≫ (exInfinityStage (m + 1)).app X :=
      congrArg (fun q => p ≫ exUnitAt ((exIterate m).obj X) ≫ q) hnext
    _ = p ≫ (exInfinityStage m).app X :=
      congrArg (fun q => p ≫ q) (exInfinityStage_succ X m)
    _ = f := hp

/--
概要：構成した Ex∞ の全ての値は Kan 複体である。
方針：horn の充填を compatible な面の族の延長へ移して Mathlib の Kan 条件を確認する。
規約：Moss 2020 Proposition 21。Kan 性を仮定せず明示的な有限段階の充填から導く。
使われ方：非 Kan 基底を扱う比較の Kan 置換。
-/
@[kerodon 00ZK, kerodon 00ZL]
instance exInfinity_kanComplex (X : SSet.{u}) : SSet.KanComplex (exInfinity.obj X) := by
  apply SSet.KanComplex.iff.mpr
  intro n i f hf
  obtain ⟨g, hg⟩ := exInfinity_hornFilling X (n + 1) (by omega) i hf.desc
  refine ⟨g, ?_⟩
  intro j hj
  rw [← hf.ι_desc j hj, ← hg, ← Category.assoc]
  simp only [SSet.horn.ι_ι]

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
