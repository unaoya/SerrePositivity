module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.DegeneracyOperators
public import SerrePositivity.DifferentialGraded.Module.Zero
/-!
概要：退化作用素の各列は、非退化因子への射影で零になる。
方針：退化ラベルへの包含と正規化射影の合成が零であることを全 Hom の後合成へ送る。
規約：全次数の加群自然性を保持する。theta が退化部分を保存することは別に証明する。
使われ方：実 bar の正規化射影と縮約作用素の整合式。
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
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgNerve R (RightModule R D))

private lemma postZero (M N P : ModuleCategory R D) (q : ℤ)
    (z : (moduleHom R D (ForgetEnrichment.to (Complex R) M)
      (ForgetEnrichment.to (Complex R) N)).X q) :
    (eHomWhiskerLeft (Complex R) M (0 : N ⟶ P)).f q z = 0 := by
  apply moduleHomElement_ext R D
    (M := ForgetEnrichment.to (Complex R) M) (N := ForgetEnrichment.to (Complex R) P)
  intro x
  rw [moduleHomWhiskerLeft_apply_π]
  have hz : (moduleEvaluation R D x).map (0 : N ⟶ P) = 0 :=
    (moduleEvaluation R D x).map_zero N P
  rw [hz, Cochain.ofHom_zero, Cochain.comp_zero, map_zero]

lemma dgCoherentBarDegenerateTargetColumn_normalizedProjection
    (s : dgCoherentBarIndex I) (t : dgCoherentBarDegenerateIndex I) (q : ℤ)
    (f : (moduleHom R D (ForgetEnrichment.to (Complex R) (dgCoherentBarFamily R D F s))
      (ForgetEnrichment.to (Complex R) (dgCoherentBarFamily R D F t.val))).X q) :
    (eHomWhiskerLeft (Complex R) (dgCoherentBarFamily R D F s)
      (dgCoherentBarNormalizedProjection R D F)).f q
      ((eHomWhiskerLeft (Complex R) (dgCoherentBarFamily R D F s)
        (Sigma.ι (dgCoherentBarFamily R D F) t.val)).f q f) = 0 := by
  have h := congrArg (fun a => a.f q f)
    (eHomWhiskerLeft_comp (Complex R) (dgCoherentBarFamily R D F s)
      (Sigma.ι (dgCoherentBarFamily R D F) t.val) (dgCoherentBarNormalizedProjection R D F))
  change (eHomWhiskerLeft (Complex R) (dgCoherentBarFamily R D F s)
      (Sigma.ι (dgCoherentBarFamily R D F) t.val ≫
        dgCoherentBarNormalizedProjection R D F)).f q f =
    (eHomWhiskerLeft (Complex R) (dgCoherentBarFamily R D F s)
      (dgCoherentBarNormalizedProjection R D F)).f q
      ((eHomWhiskerLeft (Complex R) (dgCoherentBarFamily R D F s)
        (Sigma.ι (dgCoherentBarFamily R D F) t.val)).f q f) at h
  rw [dgCoherentBarNormalizedProjection_ι_degenerate] at h
  exact h.symm.trans (postZero R D _ _ _ _ _)

lemma dgCoherentBarDegeneracyColumn_normalizedProjection {n : ℕ}
    (s : I _⦋n⦌) (i : Fin (n + 1)) :
    (eHomWhiskerLeft (Complex R) (dgCoherentBarFamily R D F ⟨n, s⟩)
      (dgCoherentBarNormalizedProjection R D F)).f (-1)
      (dgCoherentBarDegeneracyColumn R D F s i) = 0 := by
  have h := congrArg (fun f => f.f (-1) (dgCoherentBarDegeneracyBlock R D F s i))
    (eHomWhiskerLeft_comp (Complex R) (dgCoherentBarFamily R D F ⟨n, s⟩)
      (Sigma.ι (dgCoherentBarFamily R D F) (dgCoherentBarDegeneracy s i))
      (dgCoherentBarNormalizedProjection R D F))
  change (eHomWhiskerLeft (Complex R) (dgCoherentBarFamily R D F ⟨n, s⟩)
      (Sigma.ι (dgCoherentBarFamily R D F) (dgCoherentBarDegeneracy s i) ≫
        dgCoherentBarNormalizedProjection R D F)).f (-1)
      (dgCoherentBarDegeneracyBlock R D F s i) =
    (eHomWhiskerLeft (Complex R) (dgCoherentBarFamily R D F ⟨n, s⟩)
      (dgCoherentBarNormalizedProjection R D F)).f (-1)
      (dgCoherentBarDegeneracyColumn R D F s i) at h
  have hi := dgCoherentBarNormalizedProjection_ι_degenerate R D F
    ⟨dgCoherentBarDegeneracy s i, I.σ_mem_degenerate i s⟩
  rw [hi] at h
  exact h.symm.trans (postZero R D _ _ _ _ _)

lemma dgCoherentBarNormalizationHomotopyColumn_normalizedProjection (q : ℕ)
    (s : dgCoherentBarIndex I) :
    (eHomWhiskerLeft (Complex R) (dgCoherentBarFamily R D F s)
      (dgCoherentBarNormalizedProjection R D F)).f (-1)
      (dgCoherentBarNormalizationHomotopyColumn R D F q s) = 0 := by
  rcases s with ⟨n, s⟩
  unfold dgCoherentBarNormalizationHomotopyColumn
  split_ifs
  · exact map_zero _
  · simp only [Units.smul_def, map_zsmul,
      dgCoherentBarDegeneracyColumn_normalizedProjection, smul_zero]

lemma dgCoherentBarNormalizationHomotopyGraded_normalizedProjection (q : ℕ) :
    (eHomWhiskerLeft (Complex R) (dgCoherentBarGraded R D F)
      (dgCoherentBarNormalizedProjection R D F)).f (-1)
      (dgCoherentBarNormalizationHomotopyGraded R D F q) = 0 := by
  apply (dgCoherentBarHomEquiv R D F (dgCoherentBarNormalizedGraded R D F) (-1)).injective
  funext s
  rw [dgCoherentBarHomEquiv_apply]
  have h := congrArg (fun f => f.f (-1) (dgCoherentBarNormalizationHomotopyGraded R D F q))
    (eHom_whisker_exchange (Complex R) (Sigma.ι (dgCoherentBarFamily R D F) s)
      (dgCoherentBarNormalizedProjection R D F))
  change (eHomWhiskerRight (Complex R) (Sigma.ι (dgCoherentBarFamily R D F) s)
      (dgCoherentBarNormalizedGraded R D F)).f (-1)
      ((eHomWhiskerLeft (Complex R) (dgCoherentBarGraded R D F)
        (dgCoherentBarNormalizedProjection R D F)).f (-1)
        (dgCoherentBarNormalizationHomotopyGraded R D F q)) =
    (eHomWhiskerLeft (Complex R) (dgCoherentBarFamily R D F s)
      (dgCoherentBarNormalizedProjection R D F)).f (-1)
      ((eHomWhiskerRight (Complex R) (Sigma.ι (dgCoherentBarFamily R D F) s)
        (dgCoherentBarGraded R D F)).f (-1)
        (dgCoherentBarNormalizationHomotopyGraded R D F q)) at h
  rw [h, dgCoherentBarNormalizationHomotopyGraded_restrict,
    dgCoherentBarNormalizationHomotopyColumn_normalizedProjection]
  simp only [map_zero, Pi.zero_apply]

end SerrePositivity.InfinityCategories
