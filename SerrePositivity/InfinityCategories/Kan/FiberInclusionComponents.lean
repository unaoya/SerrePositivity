module

public import SerrePositivity.InfinityCategories.Kan.FiberComponents

/-!
概要：連結な底を持つ fibration の fiber 包含は連結成分で全射。
方針：零次数の完全列を π₀ との比較で移す。
規約：底の指定点を全空間の頂点の像として与える。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.6。自己 pullback の成分を fiber で代表する。
-/

@[expose] public section

universe u

open CategoryTheory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial

namespace SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：底の連結成分が一つなら fiber の包含は成分で全射。
方針：底への零次数の像が常に基点であることを完全性へ渡す。
規約：全空間と底は Kan、p は Kan fibration。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.6。連結な底の上の成分の代表。 -/
theorem fiberInclusion_piZero_surjective {E B : SSet.{u}}
    [KanComplex E] [KanComplex B] (p : E ⟶ B) [Fibration p]
    [Subsingleton (π₀ B)] (e : E _⦋0⦌) :
    Function.Surjective (mapπ₀ (fiberι p (p.app _ e))) := by
  let eE := KanHomotopyZero.equivPiZero (X := E) (x := e)
  let eF := KanHomotopyZero.equivPiZero (X := KanFiber p (p.app _ e)) (x := fiberPoint p e)
  let eB := KanHomotopyZero.equivPiZero (X := B) (x := p.app _ e)
  have : Subsingleton (KanHomotopy B 0 (p.app _ e)) :=
    ⟨fun a b => eB.injective (Subsingleton.elim _ _)⟩
  intro a
  obtain ⟨b, hb⟩ := (exact_fiber_total_zero p e (eE.symm a)).1 (Subsingleton.elim _ _)
  refine ⟨eF b, ?_⟩
  have h := congrArg eE hb
  rw [eE.apply_symm_apply] at h
  exact (KanHomotopyZero.equivPiZero_map (fiberι p (p.app _ e)) (fiberι_point p e) b).symm.trans h

/-- 概要：底の指定点の等式を明示した fiber の包含も成分で全射。
方針：指定点の等式で移送して標準の全射性へ戻す。
規約：参照頂点 e の存在を明示する。
使われ方：Kerodon §3.2.6。自己 pullback の第二因子の fiber の成分。 -/
theorem fiberInclusion_piZero_surjective_at {E B : SSet.{u}}
    [KanComplex E] [KanComplex B] (p : E ⟶ B) [Fibration p]
    [Subsingleton (π₀ B)] (e : E _⦋0⦌) (b : B _⦋0⦌) (he : p.app _ e = b) :
    Function.Surjective (mapπ₀ (fiberι p b)) := by
  subst b
  exact fiberInclusion_piZero_surjective p e

end

end SerrePositivity.KST.Spectra
