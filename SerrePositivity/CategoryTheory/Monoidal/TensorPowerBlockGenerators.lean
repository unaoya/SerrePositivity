module

public import SerrePositivity.CategoryTheory.Monoidal.TensorPowerCoherence
public import SerrePositivity.CategoryTheory.Monoidal.AdjacentTranspositions

/-!
# 次数の連結とブロック内の隣接交換

次数の移送と隣接交換を比較し、連結同型を介したブロック置換への接続を整える。
-/

@[expose] public section

universe v u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.TensorPowers

open CategoryTheory CategoryTheory.MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

/-- 隣接交換は次数とその有限添字の移送と両立する。 -/
@[reassoc] lemma adjacentIso_index_eq (X : C) {r s : ℕ} (h : r = s) (i : Fin r) :
    eqToHom (congrArg (power X) (congrArg (· + 1) h)) ≫
        (adjacentIso X s (Fin.cast h i)).hom =
      (adjacentIso X r i).hom ≫ eqToHom (congrArg (power X) (congrArg (· + 1) h)) := by
  subst s
  simp

/-- 一因子を加えた後の右ブロックの位置の計算。 -/
lemma natAdd_succ_cast (m n : ℕ) (i : Fin n) :
    Fin.cast (Nat.succ_add m n).symm (i.natAdd m).succ = i.natAdd (m + 1) := by
  apply Fin.ext
  simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- 左に空のブロックを置くときの有限添字の移送。 -/
lemma natAdd_zero_cast (n : ℕ) (i : Fin n) :
    Fin.cast (Nat.zero_add n).symm i = i.natAdd 0 := by
  apply Fin.ext
  simp

/-- 右ブロックの隣接交換は、連結後の対応する位置の交換へ送られる。 -/
lemma appendIso_adjacent_right (X : C) (m n : ℕ) (i : Fin n) :
    (power X m ◁ (adjacentIso X n i).hom) ≫ (appendIso X m (n + 1)).hom =
      (appendIso X m (n + 1)).hom ≫ (adjacentIso X (m + n) (i.natAdd m)).hom := by
  induction m with
  | zero =>
    simp only [appendIso, power, Iso.trans_hom, eqToIso.hom, Category.assoc]
    rw [leftUnitor_naturality_assoc]
    erw [← adjacentIso_index_eq X (Nat.zero_add n).symm i, natAdd_zero_cast n i]
  | succ m ih =>
    simp only [appendIso, power, Iso.trans_hom, eqToIso.hom, whiskerLeftIso_hom,
      Category.assoc]
    rw [associator_naturality_right_assoc, ← whiskerLeft_comp_assoc, ih]
    simp only [whiskerLeft_comp, Category.assoc]
    rw [← natAdd_succ_cast m n i]
    erw [adjacentIso_index_eq X (Nat.succ_add m n).symm (i.natAdd m).succ]
    simp only [adjacentIso, Fin.cases_succ, whiskerLeftIso_hom]

end SerrePositivity.TensorPowers
