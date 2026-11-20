module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FiberComponents

/-!
概要：連結な底を持つ fibration の fiber 包含は連結成分で全射。
方針：零次数の完全列を π₀ との比較で移す。
規約：底の指定点を全空間の頂点の像として与える。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.6（Tag 00WL）。自己 pullback の成分を fiber で代表する。

対応節は Kerodon 3.2（Tag 00V2）。
-/

@[expose] public section

universe u

open CategoryTheory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped _root_.Simplicial

namespace SerrePositivity.KST.Spectra
end SerrePositivity.KST.Spectra
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups
open _root_.SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：底の連結成分が一つなら fiber の包含は成分で全射。
方針：底への零次数の像が常に基点であることを完全性へ渡す。
規約：全空間と底は Kan、p は Kan fibration。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.6（Tag 00WL）。連結な底の上の成分の代表。 -/
theorem fiberInclusion_piZero_surjective {E B : SSet.{u}}
    [KanComplex E] [KanComplex B] (p : E ⟶ B) [Fibration p]
    [Subsingleton (π₀ B)] (e : E _⦋0⦌) :
    Function.Surjective (mapπ₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι p (p.app _ e))) := by
  let eE := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero.equivPiZero (X := E) (x := e)
  let eF := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero.equivPiZero (X := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanFiber p (p.app _ e)) (x := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberPoint p e)
  let eB := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero.equivPiZero (X := B) (x := p.app _ e)
  have : Subsingleton (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy B 0 (p.app _ e)) :=
    ⟨fun a b => eB.injective (Subsingleton.elim _ _)⟩
  intro a
  obtain ⟨b, hb⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.exact_fiber_total_zero p e (eE.symm a)).1 (Subsingleton.elim _ _)
  refine ⟨eF b, ?_⟩
  have h := congrArg eE hb
  rw [eE.apply_symm_apply] at h
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero.equivPiZero_map (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι p (p.app _ e)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι_point p e) b).symm.trans h

/-- 概要：底の指定点の等式を明示した fiber の包含も成分で全射。
方針：指定点の等式で移送して標準の全射性へ戻す。
規約：参照頂点 e の存在を明示する。
使われ方：Kerodon §3.2.6（Tag 00WL）。自己 pullback の第二因子の fiber の成分。 -/
theorem fiberInclusion_piZero_surjective_at {E B : SSet.{u}}
    [KanComplex E] [KanComplex B] (p : E ⟶ B) [Fibration p]
    [Subsingleton (π₀ B)] (e : E _⦋0⦌) (b : B _⦋0⦌) (he : p.app _ e = b) :
    Function.Surjective (mapπ₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι p b)) := by
  subst b
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberInclusion_piZero_surjective p e

end

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
