module
public import SerrePositivity.InfinityCategories.DGNerve.CoherentDiagramTopBoundary
/-!
概要：元の coherent 図式の辺では、最上成分の HA 境界は零である。
方針：二頂点の全集合には内部点がなく、元の HA 右辺の全ての項が消える。
規約：始点・終点の輸送を保持し、元の dg 図式の任意の辺に適用する。
使われ方：bar の最初の prefix 係数の閉性と一次元列の MC 式。
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

lemma coherentDiagramTopBoundary_edge (s : I _⦋1⦌) :
    coherentDiagramTopBoundary F s = 0 := by
  have hz : (coherentDiagramSimplex F s).toSimplexData.rhs Finset.univ 0 (Fin.last 1)
      (-(0 : ℤ)) (coherentDiagramTop_card 0) (coherentDiagramTop_min 0)
      (coherentDiagramTop_max 0) (by simp) = 0 := by
    unfold SimplexData.rhs
    apply Finset.sum_eq_zero
    intro j _
    split_ifs with h
    · have h₀ : 0 < j.val.val := h.1
      have h₁ : j.val.val < 1 := h.2
      omega
    · rfl
  let T := gradedHomTransport (A := R) (D := C)
    (coherentDiagramSimplex_obj F s (0 : Fin 2))
    (coherentDiagramSimplex_obj F s (Fin.last 1))
    (rfl : -(0 : ℤ) + 1 = -(0 : ℤ) + 1)
  exact (congrArg T hz).trans T.map_zero

end SerrePositivity.InfinityCategories.DGNerve
