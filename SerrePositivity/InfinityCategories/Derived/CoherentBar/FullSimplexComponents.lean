module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.FullSimplexSigns
public import SerrePositivity.InfinityCategories.DGNerve.PinchedTerms
/-!
概要：全体 HA 項の削除成分と左右切断を、任意の内部頂点で取り出す。
方針：既存の成分演算に全頂点集合を代入し、濃度の式で次数を比較する。
規約：任意の dg 圏に適用し、方程式を仮定しない。
使われ方：元の単体側の HA 項の後合成による因数分解。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable {R : Type u} [CommRing R] {C : Type v} [DGCategory R C]

def dgCoherentBarFullErase {n : ℕ} (s : SimplexData R C (n + 1)) (i : Fin n) :=
  s.erasedComponent Finset.univ 0 (Fin.last (n + 1)) (-(n : ℤ))
    (coherentDiagramTop_card n) (coherentDiagramTop_min n) (coherentDiagramTop_max n)
    (by simp; omega) i.succ.castSucc (Finset.mem_univ _)
    (Fin.castSucc_lt_castSucc_iff.mpr (Fin.succ_pos i)) (Fin.castSucc_lt_last _)

def dgCoherentBarFullLeft {n : ℕ} (s : SimplexData R C (n + 1)) (i : Fin n) :=
  s.cutLeft Finset.univ 0 (coherentDiagramTop_card n) (coherentDiagramTop_min n)
    i.succ.castSucc (Finset.mem_univ _)
    (Fin.castSucc_lt_castSucc_iff.mpr (Fin.succ_pos i))

def dgCoherentBarFullRight {n : ℕ} (s : SimplexData R C (n + 1)) (i : Fin n) :=
  s.cutRight Finset.univ (Fin.last (n + 1)) (coherentDiagramTop_card n)
    (coherentDiagramTop_max n) i.succ.castSucc (Finset.mem_univ _) (Fin.castSucc_lt_last _)

lemma dgCoherentBarFullLeft_card (n : ℕ) (i : Fin n) :
    ((Finset.univ : Finset (Fin (n + 2))).filter (· ≤ i.succ.castSucc)).card = i.val + 2 := by
  rw [dgCoherentBarPrefix_card (n + 1) i.succ.castSucc]
  rfl

lemma dgCoherentBarFullRight_card (n : ℕ) (i : Fin n) :
    ((Finset.univ : Finset (Fin (n + 2))).filter (i.succ.castSucc ≤ ·)).card =
      n - i.val + 1 := by
  rw [dgCoherentBarTail_card (n + 1) i.succ.castSucc]
  simp only [Fin.val_castSucc, Fin.val_succ]
  omega

lemma dgCoherentBarFullTerm_eq {n : ℕ} (s : SimplexData R C (n + 1)) (i : Fin n) :
    dgCoherentBarFullTerm s i =
      (((Finset.univ : Finset (Fin (n + 2))).filter (i.succ.castSucc < ·)).card : ℤ).negOnePow •
        (dgCoherentBarFullErase s i -
          compose R (dgCoherentBarFullRight s i) (dgCoherentBarFullLeft s i)
            (by
              change (2 - (((Finset.univ : Finset (Fin (n + 2))).filter
                (· ≤ i.succ.castSucc)).card : ℤ)) +
                (2 - (((Finset.univ : Finset (Fin (n + 2))).filter
                  (i.succ.castSucc ≤ ·)).card : ℤ)) = -(n : ℤ) + 1
              rw [dgCoherentBarFullLeft_card, dgCoherentBarFullRight_card]
              have := i.isLt
              push_cast
              omega)) := rfl

end SerrePositivity.InfinityCategories
