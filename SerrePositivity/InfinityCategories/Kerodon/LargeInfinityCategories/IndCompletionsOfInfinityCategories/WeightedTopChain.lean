module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.NerveConstantEvaluation

/-!
概要：最大添字への weighted 図式の輸送に使う、元の射列とその係数の同時収縮。
方針：時刻零では元の添字、時刻一では最大添字を取り、同じ上向き射で係数を運ぶ。
規約：係数関手の射に可逆性を要求しない。使われ方：下区間上の全 weighted 図式の収縮。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
variable {I : Type u} [PartialOrder I] [OrderTop I]

/-- 元の射列を指定された時刻に従って最大添字へ送る単調写像。 -/
def weightedTopChainOrderHom {n : ℕ} (σ : ComposableArrows I n)
    (t : Fin (n + 1) →o Fin 2) : Fin (n + 1) →o I where
  toFun j := if t j = 0 then σ.obj j else ⊤
  monotone' {a b} h := by
    dsimp only
    split_ifs with ha hb hb
    · exact leOfHom (σ.map (homOfLE h))
    · exact le_top
    · have ht := t.monotone h
      rw [hb] at ht
      exact (ha (le_antisymm ht (Fin.zero_le _))).elim
    · exact le_rfl

/-- 同じ最大添字への輸送を、通常の圏の射列として束ねる。 -/
def weightedTopChain {n : ℕ} (σ : ComposableArrows I n) (t : Fin (n + 1) →o Fin 2) :
    ComposableArrows I n :=
  (weightedTopChainOrderHom σ t).monotone.functor

/-- 各元の添字から、同じ時刻における輸送後の添字への上向き射。 -/
lemma le_weightedTopChain {n : ℕ} (σ : ComposableArrows I n)
    (t : Fin (n + 1) →o Fin 2) (j : Fin (n + 1)) : σ.obj j ≤ (weightedTopChain σ t).obj j := by
  change σ.obj j ≤ if t j = 0 then σ.obj j else ⊤
  split_ifs
  · exact le_rfl
  · exact le_top

/-- 元の係数図式を、同じ時刻の添字収縮に従って送る全自然変換。 -/
def weightedTopChainCoefficient (F : I ⥤ SSet.{u}) {n : ℕ}
    (σ : ComposableArrows I n) (t : Fin (n + 1) →o Fin 2) :
    σ ⋙ F ⟶ weightedTopChain σ t ⋙ F where
  app j := F.map (homOfLE (le_weightedTopChain σ t j))
  naturality a b f := by
    change F.map (σ.map f) ≫ F.map _ = F.map _ ≫ F.map ((weightedTopChain σ t).map f)
    rw [← F.map_comp, ← F.map_comp]
    exact congrArg F.map (Subsingleton.elim _ _)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
