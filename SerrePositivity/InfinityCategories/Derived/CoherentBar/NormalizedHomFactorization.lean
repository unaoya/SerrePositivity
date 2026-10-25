module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.NormalizedHomotopyImage
/-!
概要：退化因子への制限が零の全次数 Hom は、同じ非退化直和への射影を通る。
方針：元の全単体の Hom 直積同値で判定し、各包含と正規化射影の合成を照合する。
規約：閉次数零に限らず、全 dg 自然な斉次要素を扱う。
使われ方：theta の正規化商への降下と、商微分の MC 方程式。
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

lemma dgCoherentBarHom_precompose_comp {A B C N : ModuleCategory R D}
    (f : A ⟶ B) (g : B ⟶ C) (q : ℤ)
    (z : (moduleHom R D (ForgetEnrichment.to (Complex R) C)
      (ForgetEnrichment.to (Complex R) N)).X q) :
    (eHomWhiskerRight (Complex R) f N).f q
      ((eHomWhiskerRight (Complex R) g N).f q z) =
    (eHomWhiskerRight (Complex R) (f ≫ g) N).f q z := by
  have h := congrArg (fun a => a.f q z) (eHomWhiskerRight_comp (Complex R) f g N)
  exact h.symm

private lemma preZero (M N P : ModuleCategory R D) (q : ℤ)
    (z : (moduleHom R D (ForgetEnrichment.to (Complex R) N)
      (ForgetEnrichment.to (Complex R) P)).X q) :
    (eHomWhiskerRight (Complex R) (0 : M ⟶ N) P).f q z = 0 := by
  apply moduleHomElement_ext R D
    (M := ForgetEnrichment.to (Complex R) M) (N := ForgetEnrichment.to (Complex R) P)
  intro x
  rw [moduleHomWhiskerRight_apply_π]
  have hz : (moduleEvaluation R D x).map (0 : M ⟶ N) = 0 :=
    (moduleEvaluation R D x).map_zero M N
  rw [hz, Cochain.ofHom_zero, Cochain.zero_comp, map_zero]

variable {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgNerve R (RightModule R D))

lemma dgCoherentBarHom_factor_normalized (N : ModuleCategory R D) (q : ℤ)
    (z : (moduleHom R D (ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
      (ForgetEnrichment.to (Complex R) N)).X q)
    (hz : ∀ s : dgCoherentBarDegenerateIndex I,
      (eHomWhiskerRight (Complex R) (Sigma.ι (dgCoherentBarFamily R D F) s.val) N).f q z = 0) :
    (eHomWhiskerRight (Complex R) (dgCoherentBarNormalizedProjection R D F) N).f q
      ((eHomWhiskerRight (Complex R) (dgCoherentBarNormalizedInclusion R D F) N).f q z) = z := by
  classical
  apply (dgCoherentBarHomEquiv R D F N q).injective
  funext s
  rw [dgCoherentBarHomEquiv_apply, dgCoherentBarHomEquiv_apply,
    dgCoherentBarHom_precompose_comp R D]
  by_cases hs : s.2 ∈ I.nonDegenerate s.1
  · have hi := dgCoherentBarNormalizedProjection_ι R D F ⟨s, hs⟩
    rw [hi, dgCoherentBarHom_precompose_comp R D, dgCoherentBarNormalizedInclusion_ι]
  · have hd : s.2 ∈ I.degenerate s.1 := by
      simpa only [SSet.nonDegenerate, Set.mem_compl_iff, not_not] using hs
    rw [dgCoherentBarNormalizedProjection_ι_degenerate R D F ⟨s, hd⟩,
      preZero R D, hz ⟨s, hd⟩]

end SerrePositivity.InfinityCategories
