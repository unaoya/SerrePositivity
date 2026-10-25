module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentLayerFaceHomologyLegs
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentNaturalLayerHomology
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentPositiveFaceCoefficient
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentZeroFaceCoefficient
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentNondegLayerColumns

/-!
概要：実層の各符号つき面のホモロジー行列を、非退化 H(G) bar の面行列へ同定する。
方針：同じ非退化ラベルの包含公式と、面・辺の実係数比較を合わせる。
規約：元の実包含・正規化射影・次数輸送を保持する。
使われ方：一次ホモロジー複体全体の微分の一致。
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
  {J : Type u} [PartialOrder J]
  (G : (SSet.uliftFunctor.{max (u + 1) v, u}).obj (nerve J) ⟶
    dgNerve R (RightModule R D))

lemma dgCoherentBarLayerFaceHomology_matrix_succ {n : ℕ}
    (s : (nerve J).nonDegenerate (n + 1)) (i : Fin (n + 1)) (x : D) (q : ℤ) :
    dgDegreeOneHomologyMap R (dgCoherentBarLayerFaceCochain R D G s.val i.succ x)
      (dgCoherentBarLayerFaceCochain_closed R D G s.val i.succ x) q ≫
      (dgCoherentBarNaturalLayerHomologyIso R D G x n (q + 1) (q + ((n : ℤ) + 1)) (by omega)).hom =
    (dgComplexShiftHomologyIso R ((dgCoherentBarSource R D G ⟨n + 1, s.val⟩).obj (Opposite.op x))
      ((n : ℤ) + 1) q (q + ((n : ℤ) + 1)) (by omega)).hom ≫
      (dgCoherentBarSourceHomologyIso R D G x (q + ((n : ℤ) + 1)) (n + 1) s.val).hom ≫
        Sigma.ι (dgHomologyBarNondegFamily R
          (dgCoherentBarHomologyDiagram R D G x (q + ((n : ℤ) + 1))) (n + 1)) s ≫
          dgHomologyBarNondegFaceMap R
            (dgCoherentBarHomologyDiagram R D G x (q + ((n : ℤ) + 1))) n i.succ := by
  let t := dgHomologyBarNondegFace s i.succ
  have hi : Sigma.ι (dgCoherentBarFamily R D G) (dgCoherentBarFace s.val i.succ) ≫
      dgCoherentBarNormalizedProjection R D G ≫ dgCoherentBarLayerProjection R D G n =
    Sigma.ι (dgCoherentBarLayerFamily R D G n) (dgCoherentBarLayerIndexEquiv (nerve J) n t) :=
    dgCoherentBarNormalizedProjection_toLayer_ι R D G n t
  rw [dgCoherentBarLayerFaceHomology_succ, hi, Category.assoc,
    dgCoherentBarNaturalLayerHomologyIso_ι, dgHomologyBarNondegFaceMap_ι]
  simpa only [t, dgHomologyBarNondegFace, dgCoherentBarFace, Category.assoc] using! congrArg
    (fun f => f ≫ Sigma.ι (dgHomologyBarNondegFamily R
      (dgCoherentBarHomologyDiagram R D G x (q + ((n : ℤ) + 1))) n) t)
    (dgCoherentBarSignedPositiveFaceCoefficient R D G s.val i x q)

set_option maxHeartbeats 800000 in
-- 後尾ラベルの依存等号輸送と実層包含を照合する局所上限。
lemma dgCoherentBarLayerFaceHomology_matrix_zero {n : ℕ}
    (s : (nerve J).nonDegenerate (n + 1)) (x : D) (q : ℤ) :
    dgDegreeOneHomologyMap R (dgCoherentBarLayerFaceCochain R D G s.val 0 x)
      (dgCoherentBarLayerFaceCochain_closed R D G s.val 0 x) q ≫
      (dgCoherentBarNaturalLayerHomologyIso R D G x n (q + 1) (q + ((n : ℤ) + 1)) (by omega)).hom =
    (dgComplexShiftHomologyIso R ((dgCoherentBarSource R D G ⟨n + 1, s.val⟩).obj (Opposite.op x))
      ((n : ℤ) + 1) q (q + ((n : ℤ) + 1)) (by omega)).hom ≫
      (dgCoherentBarSourceHomologyIso R D G x (q + ((n : ℤ) + 1)) (n + 1) s.val).hom ≫
        Sigma.ι (dgHomologyBarNondegFamily R
          (dgCoherentBarHomologyDiagram R D G x (q + ((n : ℤ) + 1))) (n + 1)) s ≫
          dgHomologyBarNondegFaceMap R
            (dgCoherentBarHomologyDiagram R D G x (q + ((n : ℤ) + 1))) n 0 := by
  let t := dgHomologyBarNondegFace s 0
  let h0 := dgCoherentBarTail_one_eq_face_zero s.val
  have hi : Sigma.ι (dgCoherentBarFamily R D G) (dgCoherentBarTail s.val 1 (by omega)) ≫
      dgCoherentBarNormalizedProjection R D G ≫ dgCoherentBarLayerProjection R D G n =
    eqToHom (congrArg (dgCoherentBarFamily R D G) h0) ≫
      Sigma.ι (dgCoherentBarLayerFamily R D G n) (dgCoherentBarLayerIndexEquiv (nerve J) n t) := by
    have hraw := congrArg
      (fun f : dgCoherentBarFamily R D G (dgCoherentBarTail s.val 1 (by omega)) ⟶
          dgCoherentBarGraded R D G =>
        f ≫ dgCoherentBarNormalizedProjection R D G ≫ dgCoherentBarLayerProjection R D G n)
      (Sigma.eqToHom_comp_ι (dgCoherentBarFamily R D G) h0.symm).symm
    simp only [Category.assoc] at hraw
    have hface := congrArg
      (fun f : dgCoherentBarFamily R D G ⟨n, t.val⟩ ⟶ dgCoherentBarLayerGraded R D G n =>
        eqToHom (congrArg (dgCoherentBarFamily R D G) h0) ≫ f)
      (dgCoherentBarNormalizedProjection_toLayer_ι R D G n t)
    exact hraw.trans hface
  rw [dgCoherentBarLayerFaceHomology_zero, hi, CategoryTheory.Functor.map_comp,
    HomologicalComplex.homologyMap_comp]
  simp only [Category.assoc]
  rw [dgCoherentBarNaturalLayerHomologyIso_ι, dgHomologyBarNondegFaceMap_ι]
  simpa only [t, dgHomologyBarNondegFace, dgCoherentBarFace, Category.assoc] using! congrArg
    (fun f => f ≫ Sigma.ι (dgHomologyBarNondegFamily R
      (dgCoherentBarHomologyDiagram R D G x (q + ((n : ℤ) + 1))) n) t)
    (dgCoherentBarSignedZeroFaceCoefficient R D G s.val x q)

end SerrePositivity.InfinityCategories
