module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeCoordinates
/-!
概要：全頂点集合の HA 右辺を、内部頂点だけの有限和として表す。
方針：既存の右辺から両端の零項を除き、内部頂点を Fin n で列挙する。
規約：任意の dg 圏と零個の内部頂点を含み、全成分と符号を保持する。
使われ方：混合 HA 方程式を元の単体とパラメーターの二つの有限和へ分ける。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable {R : Type u} [CommRing R] {C : Type v} [DGCategory R C]

def dgCoherentBarFullTerm {n : ℕ} (s : SimplexData R C (n + 1)) (i : Fin n) :
    GradedHom R (s.obj 0) (s.obj (Fin.last (n + 1))) (-(n : ℤ) + 1) :=
  s.term Finset.univ 0 (Fin.last (n + 1)) (-(n : ℤ))
    (coherentDiagramTop_card n) (coherentDiagramTop_min n) (coherentDiagramTop_max n)
    (by simp; omega) i.succ.castSucc (Finset.mem_univ _)
    (Fin.castSucc_lt_castSucc_iff.mpr (Fin.succ_pos i)) (Fin.castSucc_lt_last _)

lemma dgCoherentBarFullSimplex_rhs {n : ℕ} (s : SimplexData R C (n + 1)) :
    s.rhs Finset.univ 0 (Fin.last (n + 1)) (-(n : ℤ)) (coherentDiagramTop_card n)
      (coherentDiagramTop_min n) (coherentDiagramTop_max n) (by simp; omega) =
      ∑ i : Fin n, dgCoherentBarFullTerm s i := by
  unfold SimplexData.rhs
  rw [Finset.sum_coe_sort_eq_attach, Finset.sum_attach_univ, Fin.sum_univ_castSucc]
  simp only [lt_self_iff_false, and_false, dite_false, add_zero]
  rw [Fin.sum_univ_succ]
  simp only [Fin.castSucc_zero, lt_self_iff_false, false_and, dite_false, zero_add,
    Fin.castSucc_lt_last, and_true, dgCoherentBarFullTerm]
  apply Finset.sum_congr rfl
  intro i _
  rw [dite_eq_left (show (0 : Fin (n + 2)) < i.succ.castSucc from
    Fin.castSucc_lt_castSucc_iff.mpr (Fin.succ_pos i))]

lemma dgCoherentBarFullSimplex_equation {n : ℕ} (s : DGNerve.Simplex R C (n + 1)) :
    differential R (s.hom Finset.univ 0 (Fin.last (n + 1)) (-(n : ℤ))
      (coherentDiagramTop_card n) (coherentDiagramTop_min n) (coherentDiagramTop_max n)
      (by simp; omega)) = ∑ i : Fin n, dgCoherentBarFullTerm s.toSimplexData i := by
  rw [s.equation, dgCoherentBarFullSimplex_rhs]

lemma dgCoherentBarFullSimplex_rhs_split {n m : ℕ}
    (s : SimplexData R C (n + m + 1)) :
    s.rhs Finset.univ 0 (Fin.last (n + m + 1)) (-((n + m : ℕ) : ℤ))
      (coherentDiagramTop_card (n + m)) (coherentDiagramTop_min (n + m))
      (coherentDiagramTop_max (n + m)) (by simp; omega) =
      (∑ i : Fin n, dgCoherentBarFullTerm s (i.castAdd m)) +
        ∑ j : Fin m, dgCoherentBarFullTerm s (j.natAdd n) := by
  rw [dgCoherentBarFullSimplex_rhs, Fin.sum_univ_add]

end SerrePositivity.InfinityCategories
