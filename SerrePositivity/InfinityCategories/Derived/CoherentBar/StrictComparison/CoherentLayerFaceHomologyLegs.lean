module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentLayerFaceHomologySum
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.DegreeOneHomologyNaturality
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentFaceBlockHomology
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentPrefixBlockHomology

/-!
概要：符号つき実層の各面のホモロジー射をブロックと実包含の合成へ分ける。
方針：次数一ホモロジー射の閉零射に対する後自然性を使う。
規約：実 raw 包含・正規化射影・層射影を保持する。
使われ方：各係数の比較を層の直和ホモロジー同型へ送る。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
open HomologicalComplex CochainComplex HomComplex
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (G : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgNerve R (RightModule R D))

lemma dgCoherentBarLayerFaceHomology_succ {n : ℕ} (s : I _⦋n + 1⦌)
    (i : Fin (n + 1)) (x : D) (q : ℤ) :
    dgDegreeOneHomologyMap R (dgCoherentBarLayerFaceCochain R D G s i.succ x)
      (dgCoherentBarLayerFaceCochain_closed R D G s i.succ x) q =
    dgDegreeOneHomologyMap R (dgCoherentBarSignedFaceCochain R D G s i x)
      (dgCoherentBarSignedFaceCochain_closed R D G s i x) q ≫
        HomologicalComplex.homologyMap ((moduleEvaluation R D x).map
          (Sigma.ι (dgCoherentBarFamily R D G) (dgCoherentBarFace s i.succ) ≫
            dgCoherentBarNormalizedProjection R D G ≫ dgCoherentBarLayerProjection R D G n))
              (q + 1) := by
  symm
  apply dgDegreeOneHomologyMap_post R
    ((moduleEvaluation R D x).map
      (Sigma.ι (dgCoherentBarFamily R D G) (dgCoherentBarFace s i.succ) ≫
        dgCoherentBarNormalizedProjection R D G ≫ dgCoherentBarLayerProjection R D G n))
    (dgCoherentBarSignedFaceCochain R D G s i x) (dgCoherentBarSignedFaceCochain_closed R D G s i x)
    (dgCoherentBarLayerFaceCochain R D G s i.succ x)
    (dgCoherentBarLayerFaceCochain_closed R D G s i.succ x) q
  dsimp only [dgCoherentBarLayerFaceCochain, dgCoherentBarSignedLayerFace, Fin.cases_succ,
    dgCoherentBarSignedFaceCochain]
  erw [moduleHomWhiskerLeft_apply_π, Cochain.comp_zero_cochain_v, Cochain.ofHom_v]
  simp only [Units.smul_def, map_zsmul]

lemma dgCoherentBarLayerFaceHomology_zero {n : ℕ} (s : I _⦋n + 1⦌) (x : D) (q : ℤ) :
    dgDegreeOneHomologyMap R (dgCoherentBarLayerFaceCochain R D G s 0 x)
      (dgCoherentBarLayerFaceCochain_closed R D G s 0 x) q =
    dgDegreeOneHomologyMap R (dgCoherentBarSignedPrefixCochain R D G s x)
      (dgCoherentBarSignedPrefixCochain_closed R D G s x) q ≫
        HomologicalComplex.homologyMap ((moduleEvaluation R D x).map
          (Sigma.ι (dgCoherentBarFamily R D G) (dgCoherentBarTail s 1 (by omega)) ≫
            dgCoherentBarNormalizedProjection R D G ≫ dgCoherentBarLayerProjection R D G n))
              (q + 1) := by
  symm
  apply dgDegreeOneHomologyMap_post R
    ((moduleEvaluation R D x).map
      (Sigma.ι (dgCoherentBarFamily R D G) (dgCoherentBarTail s 1 (by omega)) ≫
        dgCoherentBarNormalizedProjection R D G ≫ dgCoherentBarLayerProjection R D G n))
    (dgCoherentBarSignedPrefixCochain R D G s x) (dgCoherentBarSignedPrefixCochain_closed R D G s x)
    (dgCoherentBarLayerFaceCochain R D G s 0 x)
    (dgCoherentBarLayerFaceCochain_closed R D G s 0 x) q
  dsimp only [dgCoherentBarLayerFaceCochain, dgCoherentBarSignedLayerFace, Fin.cases_zero,
    dgCoherentBarSignedPrefixCochain]
  erw [moduleHomWhiskerLeft_apply_π, Cochain.comp_zero_cochain_v, Cochain.ofHom_v]
  simp only [Units.smul_def, map_zsmul]

end SerrePositivity.InfinityCategories
