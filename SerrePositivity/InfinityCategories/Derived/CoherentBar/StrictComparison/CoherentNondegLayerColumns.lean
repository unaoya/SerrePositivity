module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentLayerCoefficients
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.ShiftPostcomposition
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.HomologyBarNondegFaces

/-!
概要：非退化な実列の正規化・次元層射影を同じ層包含へ簡約する。
方針：同じラベルの包含を保持し、全 Hom の後合成の結合則を使う。
規約：実射の等号を示し、ホモロジーだけの一致へ弱めない。
使われ方：一次面列と辺列の層ホモロジー係数の比較。
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

@[reassoc]
lemma dgCoherentBarNormalizedProjection_toLayer_ι (n : ℕ) (s : I.nonDegenerate n) :
    Sigma.ι (dgCoherentBarFamily R D G) ⟨n, s.val⟩ ≫
      dgCoherentBarNormalizedProjection R D G ≫ dgCoherentBarLayerProjection R D G n =
    Sigma.ι (dgCoherentBarLayerFamily R D G n) (dgCoherentBarLayerIndexEquiv I n s) := by
  rw [← Category.assoc, dgCoherentBarNormalizedProjection_ι R D G ⟨⟨n, s.val⟩, s.property⟩]
  exact dgCoherentBarLayerProjection_ι R D G n (dgCoherentBarLayerIndexEquiv I n s)

set_option maxHeartbeats 800000 in
-- 実余積のラベル輸送と全 Hom の後合成を照合する局所上限。
lemma dgCoherentBarPostNormalizedLayerColumn {M : ModuleCategory R D} (n : ℕ)
    (s : I.nonDegenerate n) (q : ℤ)
    (z : (moduleHom R D (ForgetEnrichment.to (Complex R) M)
      (ForgetEnrichment.to (Complex R) (dgCoherentBarFamily R D G ⟨n, s.val⟩))).X q) :
    (eHomWhiskerLeft (Complex R) M
      (dgCoherentBarNormalizedProjection R D G ≫ dgCoherentBarLayerProjection R D G n)).f q
        ((eHomWhiskerLeft (Complex R) M
          (Sigma.ι (dgCoherentBarFamily R D G) ⟨n, s.val⟩)).f q z) =
    (eHomWhiskerLeft (Complex R) M
      (Sigma.ι (dgCoherentBarLayerFamily R D G n) (dgCoherentBarLayerIndexEquiv I n s))).f q z := by
  exact (dgStrictPostcompose_comp R D (T := M)
    (Sigma.ι (dgCoherentBarFamily R D G) ⟨n, s.val⟩)
    (dgCoherentBarNormalizedProjection R D G ≫ dgCoherentBarLayerProjection R D G n) z).symm.trans
      (congrArg (fun f : dgCoherentBarFamily R D G ⟨n, s.val⟩ ⟶
          dgCoherentBarLayerGraded R D G n => (eHomWhiskerLeft (Complex R) M f).f q z)
        (dgCoherentBarNormalizedProjection_toLayer_ι R D G n s))

end SerrePositivity.InfinityCategories
