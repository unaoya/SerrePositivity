module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.NativeLabelCoordinates
/-!
概要：正規化 native 単体の全頂点集合の成分を、元の単体の native 列に同定する。
方針：末端付き全先頭集合のラベルが元の単体であることを使う。
規約：元の始点と次数を異種等号で保持する。
使われ方：余錐から回収した Hom 候補の閉性を native 列の全単射で判定する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
open scoped Simplicial
variable {I : SSet.{u}}

lemma dgCoherentBarBianchiLabel_univ {n : ℕ} (s : I _⦋n⦌) :
    dgCoherentBarBianchiLabel s Finset.univ (coherentDiagramTop_card n)
      (coherentDiagramTop_max n) = ⟨n, s⟩ := by
  have h := dgCoherentBarBianchiLabel_withLast s Finset.univ n (by simp)
    Finset.univ_nonempty
  simpa only [dgCoherentBar_withLast_univ n] using
    h.trans (dgCoherentBarSubsetLabel_univ s)

variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgNerve R (RightModule R D))
  (hMC : dgCoherentBarMaurerCartan R D F)

lemma dgCoherentBarNativeSimplex_source {n : ℕ} (s : I _⦋n⦌) :
    (dgCoherentBarNativeSimplex R D F hMC s).obj 0 = dgCoherentBarSource R D F ⟨n, s⟩ := by
  have h := congrArg (fun t : DGNerve.Simplex R (RightModule R D) n => t.obj 0)
    (dgCoherentBarNativeSimplex_front R D F hMC s)
  exact h.trans (coherentDiagramSimplex_obj F s 0)

lemma dgCoherentBarNativeSimplex_full_hom_heq {n : ℕ} (s : I _⦋n⦌) :
    HEq ((dgCoherentBarNativeSimplex R D F hMC s).hom Finset.univ 0 (Fin.last (n + 1))
      (-(n : ℤ)) (coherentDiagramTop_card n) (coherentDiagramTop_min n)
      (coherentDiagramTop_max n) (by simp; omega))
      (dgCoherentBarNativeColumn R D F hMC ⟨n, s⟩) := by
  have h := dgCoherentBarNativeSimplexData_last_hom_heq R D F hMC s Finset.univ 0
    (-(n : ℤ)) (coherentDiagramTop_card n) (coherentDiagramTop_min n)
    (coherentDiagramTop_max n) (by simp)
  rw [dgCoherentBarBianchiLabel_univ] at h
  exact h

end SerrePositivity.InfinityCategories
