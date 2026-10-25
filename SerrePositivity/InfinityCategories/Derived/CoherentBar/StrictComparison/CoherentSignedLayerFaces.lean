module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentFirstLayerHom
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentFirstFaceSigns

/-!
概要：全ての一次面を、同じ直下一次元層へ値を取る符号つき実列としてまとめる。
方針：零番には一次 prefix、正の番号には面ブロックを使う。
規約：元のブロックと raw ラベルの射影を保持する。
使われ方：一次作用素を通常の交代面和へ分解する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (G : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgNerve R (RightModule R D))

def dgCoherentBarSignedLayerFace {n : ℕ} (s : I _⦋n + 1⦌) (i : Fin (n + 2)) :
    (moduleHom R D (ForgetEnrichment.to (Complex R) (dgCoherentBarFamily R D G ⟨n + 1, s⟩))
      (ForgetEnrichment.to (Complex R) (dgCoherentBarLayerGraded R D G n))).X 1 :=
  Fin.cases
    ((eHomWhiskerLeft (Complex R) (dgCoherentBarFamily R D G ⟨n + 1, s⟩)
      (Sigma.ι (dgCoherentBarFamily R D G) (dgCoherentBarTail s 1 (by omega)) ≫
        dgCoherentBarNormalizedProjection R D G ≫ dgCoherentBarLayerProjection R D G n)).f 1
          (((n : ℤ) + 1).negOnePow • dgCoherentBarPrefixBlock R D G s 0 (by omega)))
    (fun j => (eHomWhiskerLeft (Complex R) (dgCoherentBarFamily R D G ⟨n + 1, s⟩)
      (Sigma.ι (dgCoherentBarFamily R D G) (dgCoherentBarFace s j.succ) ≫
        dgCoherentBarNormalizedProjection R D G ≫ dgCoherentBarLayerProjection R D G n)).f 1
          (((n : ℤ) + 1).negOnePow • dgCoherentBarFaceBlock R D G s j)) i

lemma dgCoherentBarSignedLayerFace_d {n : ℕ} (s : I _⦋n + 1⦌) (i : Fin (n + 2)) :
    (moduleHom R D (ForgetEnrichment.to (Complex R) (dgCoherentBarFamily R D G ⟨n + 1, s⟩))
      (ForgetEnrichment.to (Complex R) (dgCoherentBarLayerGraded R D G n))).d 1 2
        (dgCoherentBarSignedLayerFace R D G s i) = 0 := by
  refine Fin.cases ?_ (fun j => ?_) i
  · dsimp only [dgCoherentBarSignedLayerFace, Fin.cases_zero]
    erw [dgStrictHom_postcompose_d R D]
    simp only [Units.smul_def, map_zsmul]
    erw [dgCoherentBarPrefixBlock_zero_d R D G s (by omega), map_zero, zsmul_zero]
  · dsimp only [dgCoherentBarSignedLayerFace, Fin.cases_succ]
    erw [dgStrictHom_postcompose_d R D]
    simp only [Units.smul_def, map_zsmul]
    erw [dgCoherentBarFaceBlock_d R D G s j, map_zero, zsmul_zero]

end SerrePositivity.InfinityCategories
