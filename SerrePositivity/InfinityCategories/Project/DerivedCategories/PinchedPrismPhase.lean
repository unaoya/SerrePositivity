module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Index

/-! # pinched prism の終端を固定する二相

概要：係数の各前面頂点の相を保ち、最後の標的頂点の相を一に固定する。
方針：Fin.lastCases と最終点固定延長の計算を使う。
規約：標的はホモトピー全体で固定する。使われ方：厳密 dg 自然変換の slice prism。
-/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories

/-- 任意の二相の最後に、固定標的の一相を追加する。 -/
def pinchedPrismPhase {n : ℕ} (β : Fin (n + 1) →o Fin 2) : Fin (n + 2) →o Fin 2 where
  toFun := Fin.lastCases 1 β
  monotone' := by
    intro a b hab
    induction a using Fin.lastCases with
    | last =>
      have hb : b = Fin.last (n + 1) := le_antisymm (Fin.le_last _) hab
      subst b
      exact le_rfl
    | cast a =>
      induction b using Fin.lastCases with
      | last =>
        simp only [Fin.lastCases_castSucc, Fin.lastCases_last]
        exact Fin.le_last (β a)
      | cast b =>
        simpa only [Fin.lastCases_castSucc] using
          β.monotone (Fin.castSucc_le_castSucc_iff.mp hab)

/-- 先頭の全頂点の相は元の二相に一致する。 -/
lemma pinchedPrismPhase_castSucc {n : ℕ} (β : Fin (n + 1) →o Fin 2) (i : Fin (n + 1)) :
    pinchedPrismPhase β i.castSucc = β i := by simp [pinchedPrismPhase]

/-- 固定標的の相は一。 -/
lemma pinchedPrismPhase_last {n : ℕ} (β : Fin (n + 1) →o Fin 2) :
    pinchedPrismPhase β (Fin.last (n + 1)) = 1 := by simp [pinchedPrismPhase]

/-- 終端固定の二相は、全ての係数の面・退化の引き戻しと可換。 -/
lemma pinchedPrismPhase_comp {m n : ℕ} (β : Fin (n + 1) →o Fin 2)
    (α : Fin (m + 1) →o Fin (n + 1)) :
    pinchedPrismPhase (β.comp α) =
      (pinchedPrismPhase β).comp (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom α) := by
  apply DFunLike.ext
  intro i
  induction i using Fin.lastCases with
  | last => simp [pinchedPrismPhase_last, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom_last]
  | cast i => simp [pinchedPrismPhase_castSucc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom_castSucc]

/-- 終端固定の二相を前面へ制限すると、元の二相を回収する。 -/
lemma pinchedPrismPhase_front {n : ℕ} (β : Fin (n + 1) →o Fin 2) :
    (pinchedPrismPhase β).comp Fin.castSuccOrderEmb.toOrderHom = β := by
  apply DFunLike.ext
  exact pinchedPrismPhase_castSucc β

/-- 全前面の相が一なら、終端固定延長も全て一。 -/
lemma pinchedPrismPhase_one (n : ℕ) :
    pinchedPrismPhase (OrderHom.const (Fin (n + 1)) (1 : Fin 2)) =
      OrderHom.const (Fin (n + 2)) (1 : Fin 2) := by
  apply DFunLike.ext
  intro i
  induction i using Fin.lastCases with
  | last => exact pinchedPrismPhase_last _
  | cast i => exact pinchedPrismPhase_castSucc _ i

end SerrePositivity.InfinityCategories.Project.DerivedCategories
