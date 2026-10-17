module

public import SerrePositivity.CategoryTheory.Simplex.Prefix

/-! # Move an initial vertex along a simplex of the standard interval -/

@[expose] public section
universe v
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory

namespace SerrePositivity.SimplexPrefix

abbrev interval : SSet.{v} := SSet.stdSimplex.obj (SimplexCategory.mk 1)

def endpoint (n : SimplexCategory) (b : Fin 2) : interval.{v}.obj (Opposite.op n) :=
  SSet.stdSimplex.objEquiv.symm (SimplexCategory.Hom.mk (OrderHom.const _ b))

def cut (n : SimplexCategory) (t : interval.{v}.obj (Opposite.op n)) :
    n ⟶ SimplexCategory.mk (n.len + 1) :=
  SimplexCategory.Hom.mk
    ⟨fun j => if (SSet.stdSimplex.objEquiv t).toOrderHom j = 0 then 0 else j.succ, by
      intro i j hij
      dsimp only
      by_cases hi : (SSet.stdSimplex.objEquiv t).toOrderHom i = 0
      · rw [ite_eq_left hi]
        exact Fin.zero_le _
      · by_cases hj : (SSet.stdSimplex.objEquiv t).toOrderHom j = 0
        · exfalso
          apply hi
          exact le_antisymm ((SSet.stdSimplex.objEquiv t).toOrderHom.monotone hij |>.trans
            (le_of_eq hj)) (Fin.zero_le _)
        · rw [ite_eq_right hi, ite_eq_right hj]
          exact Fin.succ_le_succ_iff.mpr hij⟩

lemma cut_naturality {n m : SimplexCategory} (f : m ⟶ n)
    (t : interval.{v}.obj (Opposite.op n)) :
    f ≫ cut n t = cut m (interval.map f.op t) ≫ functor.map f := by
  ext j : 3
  change (if (SSet.stdSimplex.objEquiv t).toOrderHom (f.toOrderHom j) = 0
    then 0 else (f.toOrderHom j).succ) =
      Fin.cases 0 (fun i => (f.toOrderHom i).succ)
        (if (SSet.stdSimplex.objEquiv t).toOrderHom (f.toOrderHom j) = 0 then 0 else j.succ)
  split_ifs <;> rfl

lemma cut_one (n : SimplexCategory) :
    cut n (endpoint.{v} n 1) = SimplexCategory.δ (0 : Fin (n.len + 2)) := by
  ext j : 3
  change (if (1 : Fin 2) = 0 then 0 else j.succ) = (0 : Fin (n.len + 2)).succAbove j
  rw [ite_eq_right (by decide), Fin.succAbove_zero_apply]

lemma cut_zero (n : SimplexCategory) : cut n (endpoint.{v} n 0) =
    SimplexCategory.Hom.mk (OrderHom.const _ 0) := by
  ext j : 3
  change (if (0 : Fin 2) = 0 then 0 else j.succ) = 0
  rfl

def zeroVertex (n : SimplexCategory) : SimplexCategory.mk 0 ⟶ n :=
  SimplexCategory.Hom.mk (OrderHom.const _ 0)

lemma cut_zero_factor (n : SimplexCategory) : cut n (endpoint.{v} n 0) =
    SimplexCategory.isTerminalZero.from n ≫ SimplexCategory.δ (1 : Fin 2) ≫
      functor.map (zeroVertex n) := by
  rw [cut_zero]
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext j
  have h : (SimplexCategory.isTerminalZero.from n).toOrderHom j = 0 :=
    Subsingleton.elim (α := Fin 1) _ _
  change (0 : Fin (n.len + 2)) =
    Fin.cases (0 : Fin (n.len + 2)) (fun i => ((zeroVertex n).toOrderHom i).succ)
    ((1 : Fin 2).succAbove ((SimplexCategory.isTerminalZero.from n).toOrderHom j))
  rw [h]
  rfl

end SerrePositivity.SimplexPrefix
