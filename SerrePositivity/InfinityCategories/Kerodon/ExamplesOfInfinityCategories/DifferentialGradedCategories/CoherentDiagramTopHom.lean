module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.CoherentDiagramVertices
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HomTransport
/-!
概要：元の coherent 図式の各正次元単体の最上成分と、その実微分を取り出す。
方針：HA の全頂点集合の成分を使い、始点・終点だけを元の図式の頂点へ輸送する。
規約：辺だけに制限せず、全次元の次数 −n 成分と HA 方程式を保持する。
使われ方：coherent bar 微分の prefix 成分と MC 方程式。

対応節は Kerodon 2.5（Tag 00ND）。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable {R : Type u} [CommRing R] {C : Type v} [DGCategory R C]
  {I : SSet.{u}} (F : (SSet.uliftFunctor.{v, u}).obj I ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R C)

lemma coherentDiagramTop_card (n : ℕ) :
    2 ≤ (Finset.univ : Finset (Fin (n + 2))).card := by simp

lemma coherentDiagramTop_min (n : ℕ) :
    (0 : Fin (n + 2)) = Finset.univ.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty (coherentDiagramTop_card n)) :=
  (show IsLeast ((Finset.univ : Finset (Fin (n + 2))) : Set (Fin (n + 2))) 0 from
    ⟨Finset.mem_univ _, fun a _ => Fin.zero_le a⟩).unique ((Finset.univ : Finset (Fin (n + 2))).isLeast_min' _)

lemma coherentDiagramTop_max (n : ℕ) :
    Fin.last (n + 1) = Finset.univ.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty (coherentDiagramTop_card n)) :=
  (show IsGreatest ((Finset.univ : Finset (Fin (n + 2))) : Set (Fin (n + 2))) (Fin.last (n + 1)) from
    ⟨Finset.mem_univ _, fun a _ => Fin.le_last a⟩).unique ((Finset.univ : Finset (Fin (n + 2))).isGreatest_max' _)

def coherentDiagramTopRaw {n : ℕ} (s : I _⦋n + 1⦌) :
    GradedHom R ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramSimplex F s).obj 0)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramSimplex F s).obj (Fin.last (n + 1))) (-(n : ℤ)) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramSimplex F s).hom Finset.univ 0 (Fin.last (n + 1)) (-(n : ℤ))
    (coherentDiagramTop_card n) (coherentDiagramTop_min n) (coherentDiagramTop_max n)
    (by simp; omega)

lemma coherentDiagramTopRaw_differential {n : ℕ} (s : I _⦋n + 1⦌) :
    differential R (coherentDiagramTopRaw F s) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramSimplex F s).toSimplexData.rhs Finset.univ 0 (Fin.last (n + 1))
        (-(n : ℤ)) (coherentDiagramTop_card n) (coherentDiagramTop_min n)
        (coherentDiagramTop_max n) (by simp; omega) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramSimplex F s).equation _ _ _ _ _ _ _ _

def coherentDiagramTop {n : ℕ} (s : I _⦋n + 1⦌) :
    GradedHom R (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramVertex F
      (I.map (SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ 0).op s))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramVertex F
        (I.map (SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ (Fin.last (n + 1))).op s)) (-(n : ℤ)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHomTransport (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramSimplex_obj F s 0)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramSimplex_obj F s (Fin.last (n + 1))) rfl (coherentDiagramTopRaw F s)

lemma coherentDiagramTop_differential {n : ℕ} (s : I _⦋n + 1⦌) :
    differential R (coherentDiagramTop F s) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHomTransport (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramSimplex_obj F s 0)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramSimplex_obj F s (Fin.last (n + 1))) rfl
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramSimplex F s).toSimplexData.rhs Finset.univ 0 (Fin.last (n + 1))
          (-(n : ℤ)) (coherentDiagramTop_card n) (coherentDiagramTop_min n)
          (coherentDiagramTop_max n) (by simp; omega)) := by
  rw [coherentDiagramTop, ← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHomTransport_differential, coherentDiagramTopRaw_differential]

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
