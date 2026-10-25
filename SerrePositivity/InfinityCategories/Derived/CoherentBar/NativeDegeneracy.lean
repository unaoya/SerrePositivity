module
public import SerrePositivity.InfinityCategories.DGNerve.CoherentDiagramTopHom
public import SerrePositivity.InfinityCategories.DGNerve.Computations
/-!
概要：native dg nerve 値図式の退化三角形では最上 cochain は必ず零になる。
方針：図式の単体的自然性と dg nerve の退化成分公式を使う。
規約：全単体を独立因子に持つ未正規化 bar の包含を余錐成分と即断しない。
使われ方：bar の native 余錐に必要な退化整合性の検査。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable {R : Type u} [CommRing R] {C : Type v} [DGCategory R C]
  {I : SSet.{u}} (F : (SSet.uliftFunctor.{v, u}).obj I ⟶ dgNerve R C)

lemma dgCoherentBar_native_degenerateTriangle (s : I _⦋1⦌) (i : Fin 2) :
    coherentDiagramTopRaw F (I.σ i s) = 0 := by
  have h : coherentDiagramSimplex F (I.σ i s) =
      (dgNerve R C).σ i (coherentDiagramSimplex F s) :=
    coherentDiagramSimplex_map F i.predAboveOrderHom s
  unfold coherentDiagramTopRaw
  rw [h]
  exact dgNerve.σ_hom_eq_zero R C i (coherentDiagramSimplex F s)
    Finset.univ 0 (Fin.last 2) (-1) (coherentDiagramTop_card 1)
    (coherentDiagramTop_min 1) (coherentDiagramTop_max 1) (by simp)
    (Finset.mem_univ _) (Finset.mem_univ _) (by simp)

lemma dgCoherentBar_native_degenerateTop {n : ℕ} (s : I _⦋n + 1⦌)
    (i : Fin (n + 2)) : coherentDiagramTopRaw F (I.σ i s) = 0 := by
  have h : coherentDiagramSimplex F (I.σ i s) =
      (dgNerve R C).σ i (coherentDiagramSimplex F s) :=
    coherentDiagramSimplex_map F i.predAboveOrderHom s
  unfold coherentDiagramTopRaw
  rw [h]
  exact dgNerve.σ_hom_eq_zero R C i (coherentDiagramSimplex F s)
    Finset.univ 0 (Fin.last (n + 2)) (-((n + 1 : ℕ) : ℤ))
    (coherentDiagramTop_card (n + 1)) (coherentDiagramTop_min (n + 1))
    (coherentDiagramTop_max (n + 1)) (by simp)
    (Finset.mem_univ _) (Finset.mem_univ _) (by simp)

lemma dgCoherentBar_native_degenerateTop_transported {n : ℕ} (s : I _⦋n + 1⦌)
    (i : Fin (n + 2)) : coherentDiagramTop F (I.σ i s) = 0 := by
  unfold coherentDiagramTop
  rw [dgCoherentBar_native_degenerateTop]
  exact map_zero _

end SerrePositivity.InfinityCategories
