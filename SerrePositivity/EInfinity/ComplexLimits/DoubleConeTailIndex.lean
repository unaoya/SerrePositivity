module
public import SerrePositivity.InfinityCategories.Core.PinchedSlice
public import SerrePositivity.InfinityCategories.DGNerve.PinchedReindexIndex

/-!
概要：実二重 cone から最初の先端を除く作用素を、既存の終点固定延長で指定する。
方針：後続埋め込みを延長し、終端と前面および先頭添字の回復を計算する。
規約：元の頂点順序と終端を保持する。使われ方：通常右余錐の実単体との比較。
-/
@[expose] public section
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory
open SerrePositivity.InfinityCategories

def doubleConeTailOrderHom (n : ℕ) : Fin (n + 2) →o Fin (n + 3) :=
  InfinityCategories.PinchedHom.extendOrderHom (Fin.succOrderEmb (n + 1)).toOrderHom

lemma doubleConeTailOrderHom_castSucc (n : ℕ) (i : Fin (n + 1)) :
    doubleConeTailOrderHom n i.castSucc = i.succ.castSucc :=
  InfinityCategories.PinchedHom.extendOrderHom_castSucc _ i

lemma doubleConeTailOrderHom_last (n : ℕ) :
    doubleConeTailOrderHom n (Fin.last (n + 1)) = Fin.last (n + 2) :=
  InfinityCategories.PinchedHom.extendOrderHom_last _

lemma doubleConeTailOrderHom_predAbove (n : ℕ) (i : Fin (n + 2))
    (hi : i ≠ Fin.last (n + 1)) :
    (Fin.last (n + 1)).predAboveOrderHom (doubleConeTailOrderHom n i) =
      ((Fin.last n).predAboveOrderHom i).succ := by
  induction i using Fin.lastCases with
  | last => exact False.elim (hi rfl)
  | cast i =>
    rw [doubleConeTailOrderHom_castSucc]
    exact Fin.predAbove_last_castSucc.trans (congrArg Fin.succ Fin.predAbove_last_castSucc.symm)

end SerrePositivity.EInfinity.ComplexLimits
