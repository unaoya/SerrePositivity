module
public import SerrePositivity.InfinityCategories.DGNerve.CoherentDiagramVertices
public import SerrePositivity.InfinityCategories.DGNerve.HomTransport
/-!
概要：元の coherent 図式の各正次元単体の最上成分と、その実微分を取り出す。
方針：HA の全頂点集合の成分を使い、始点・終点だけを元の図式の頂点へ輸送する。
規約：辺だけに制限せず、全次元の次数 −n 成分と HA 方程式を保持する。
使われ方：coherent bar 微分の prefix 成分と MC 方程式。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.DGNerve
open CategoryTheory DifferentialGraded SSet
open scoped Simplicial
variable {R : Type u} [CommRing R] {C : Type v} [DGCategory R C]
  {I : SSet.{u}} (F : (SSet.uliftFunctor.{v, u}).obj I ⟶ dgNerve R C)

lemma coherentDiagramTop_card (n : ℕ) :
    2 ≤ (Finset.univ : Finset (Fin (n + 2))).card := by simp

lemma coherentDiagramTop_min (n : ℕ) :
    (0 : Fin (n + 2)) = Finset.univ.min' (Index.nonempty (coherentDiagramTop_card n)) :=
  (show IsLeast ((Finset.univ : Finset (Fin (n + 2))) : Set (Fin (n + 2))) 0 from
    ⟨Finset.mem_univ _, fun a _ => Fin.zero_le a⟩).unique ((Finset.univ : Finset (Fin (n + 2))).isLeast_min' _)

lemma coherentDiagramTop_max (n : ℕ) :
    Fin.last (n + 1) = Finset.univ.max' (Index.nonempty (coherentDiagramTop_card n)) :=
  (show IsGreatest ((Finset.univ : Finset (Fin (n + 2))) : Set (Fin (n + 2))) (Fin.last (n + 1)) from
    ⟨Finset.mem_univ _, fun a _ => Fin.le_last a⟩).unique ((Finset.univ : Finset (Fin (n + 2))).isGreatest_max' _)

def coherentDiagramTopRaw {n : ℕ} (s : I _⦋n + 1⦌) :
    GradedHom R ((coherentDiagramSimplex F s).obj 0)
      ((coherentDiagramSimplex F s).obj (Fin.last (n + 1))) (-(n : ℤ)) :=
  (coherentDiagramSimplex F s).hom Finset.univ 0 (Fin.last (n + 1)) (-(n : ℤ))
    (coherentDiagramTop_card n) (coherentDiagramTop_min n) (coherentDiagramTop_max n)
    (by simp; omega)

lemma coherentDiagramTopRaw_differential {n : ℕ} (s : I _⦋n + 1⦌) :
    differential R (coherentDiagramTopRaw F s) =
      (coherentDiagramSimplex F s).toSimplexData.rhs Finset.univ 0 (Fin.last (n + 1))
        (-(n : ℤ)) (coherentDiagramTop_card n) (coherentDiagramTop_min n)
        (coherentDiagramTop_max n) (by simp; omega) :=
  (coherentDiagramSimplex F s).equation _ _ _ _ _ _ _ _

def coherentDiagramTop {n : ℕ} (s : I _⦋n + 1⦌) :
    GradedHom R (coherentDiagramVertex F
      (I.map (SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ 0).op s))
      (coherentDiagramVertex F
        (I.map (SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ (Fin.last (n + 1))).op s)) (-(n : ℤ)) :=
  gradedHomTransport (coherentDiagramSimplex_obj F s 0)
    (coherentDiagramSimplex_obj F s (Fin.last (n + 1))) rfl (coherentDiagramTopRaw F s)

lemma coherentDiagramTop_differential {n : ℕ} (s : I _⦋n + 1⦌) :
    differential R (coherentDiagramTop F s) =
      gradedHomTransport (coherentDiagramSimplex_obj F s 0)
        (coherentDiagramSimplex_obj F s (Fin.last (n + 1))) rfl
        ((coherentDiagramSimplex F s).toSimplexData.rhs Finset.univ 0 (Fin.last (n + 1))
          (-(n : ℤ)) (coherentDiagramTop_card n) (coherentDiagramTop_min n)
          (coherentDiagramTop_max n) (by simp; omega)) := by
  rw [coherentDiagramTop, ← gradedHomTransport_differential, coherentDiagramTopRaw_differential]

end SerrePositivity.InfinityCategories.DGNerve
