module

public import SerrePositivity.CommutativeAlgebra.PowTorsionCategory
public import SerrePositivity.PerfectComplex.NormalizedEuler

/-! # ホモロジー上で零となる自己射の錐と Euler 評価

錐の有限長さから元のホモロジーの有限長さを導き、既存の Euler 加法性を適用する。
零ホモトピーの存在より弱い、ホモロジーに誘導する写像の零性だけを使う。
-/

@[expose] public section
universe u
namespace SerrePositivity
open CategoryTheory Limits Pretriangulated
set_option backward.isDefEq.respectTransparency false
variable {R : Type u} [CommRing R] {J : Ideal R} (lam : NormalizedLength R J)

/-- ホモロジーに零写像を誘導する射の錐では、短完全列から長さの和の公式が得られる。 -/
theorem lambdaHomology_cone_of_homologyMap_eq_zero {P Q : CochainComplex (ModuleCat.{u} R) ℤ}
    (f : P ⟶ Q) (hz : ∀ i, HomologicalComplex.homologyMap f i = 0) (q : ℤ)
    (hQ : IsPowTorsion J (Q.homology q)) (hP : IsPowTorsion J (P.homology (q + 1))) :
    IsPowTorsion J ((Cone.cone f).homology q) ∧
      lam.len ((Cone.cone f).homology q) =
        lam.len (Q.homology q) + lam.len (P.homology (q + 1)) := by
  let S := ShortComplex.mk _ _
    (comp_eq_zero_transport (Cone.S₃ f q (q + 1) rfl)
      (Cone.e q Q) (Cone.e q (Cone.cone f)) (Cone.e (q + 1) P)
      _ (Cone.δ f q (q + 1) rfl)
      (Cone.e_naturality q (CochainComplex.mappingCone.inr f)) (Cone.δ_square f q (q + 1) rfl))
  have : Mono S.f := (Cone.exact₂ f q).mono_g (hz q)
  have : Epi S.g := (Cone.exact₁ f q (q + 1) rfl).epi_f (hz (q + 1))
  have hs : S.ShortExact := ⟨Cone.exact₃ f q (q + 1) rfl⟩
  have ht : IsPowTorsion J ((Cone.cone f).homology q) :=
    (powTorsionModule J).prop_X₂_of_shortExact hs hQ hP
  exact ⟨ht, lam.len_add_of_exact _ _ _ S.f.hom S.g.hom
    ((ModuleCat.mono_iff_injective _).mp inferInstance)
    ((ModuleCat.epi_iff_surjective _).mp inferInstance)
    (LinearMap.exact_iff.mpr hs.exact.moduleCat_range_eq_ker.symm) ht⟩

/-- ホモロジーに零写像を誘導する射では、右のホモロジーの長さは錐の長さ以下。 -/
theorem lambdaHomology_le_cone_of_homologyMap_eq_zero
    {P Q : CochainComplex (ModuleCat.{u} R) ℤ} (f : P ⟶ Q) (q : ℤ)
    (hz : HomologicalComplex.homologyMap f q = 0)
    (tC : IsPowTorsion J ((Cone.cone f).homology q)) :
    lam.len (Q.homology q) ≤ lam.len ((Cone.cone f).homology q) := by
  have : Mono (HomologicalComplex.homologyMap (CochainComplex.mappingCone.inr f) q) :=
    (Cone.exact₂ f q).mono_g hz
  exact lam.len_le_of_injective
    (HomologicalComplex.homologyMap (CochainComplex.mappingCone.inr f) q).hom
    ((ModuleCat.mono_iff_injective _).mp inferInstance) tC

/-- 錐のホモロジーの長さが有限なら、右の元のホモロジーの長さも有限。 -/
theorem lambdaHomology_ne_top_of_cone_of_homologyMap_eq_zero
    {P Q : CochainComplex (ModuleCat.{u} R) ℤ} (f : P ⟶ Q) (q : ℤ)
    (hz : HomologicalComplex.homologyMap f q = 0)
    (tC : IsPowTorsion J ((Cone.cone f).homology q))
    (lC : lam.len ((Cone.cone f).homology q) ≠ ⊤) :
    lam.len (Q.homology q) ≠ ⊤ :=
  ne_top_of_le_ne_top lC (lambdaHomology_le_cone_of_homologyMap_eq_zero lam f q hz tC)

/-- ホモロジー上で零となる自己射の錐は Euler 評価零。
元のホモロジー長の有限性は、錐から導き、未知の仮定として渡さない。 -/
theorem lambdaEuler_self_cone_eq_zero_of_homologyMap_eq_zero
    {P : CochainComplex (ModuleCat.{u} R) ℤ} (f : P ⟶ P)
    (hz : ∀ q, HomologicalComplex.homologyMap f q = 0)
    (hP : ∃ a b : ℤ, ∀ i, (i < a ∨ b < i) → IsZero (P.X i))
    (hC : ∃ a b : ℤ, ∀ i, (i < a ∨ b < i) → IsZero ((Cone.cone f).X i))
    (tP : ∀ q, IsPowTorsion J (P.homology q))
    (tC : ∀ q, IsPowTorsion J ((Cone.cone f).homology q))
    (lC : ∀ q, lam.len ((Cone.cone f).homology q) ≠ ⊤) :
    lambdaEuler lam (Cone.cone f) = 0 := by
  have lP (q : ℤ) : lam.len (P.homology q) ≠ ⊤ :=
    lambdaHomology_ne_top_of_cone_of_homologyMap_eq_zero lam f q (hz q) (tC q) (lC q)
  simpa only [sub_self] using lambdaEuler_cone lam f hP hC tP tP tC lP lP lC

/-- ホモロジー上で零となる射では、錐の一つ前の次数が左のホモロジーへ全射する。 -/
theorem lambdaHomology_le_cone_prev_of_homologyMap_eq_zero
    {P Q : CochainComplex (ModuleCat.{u} R) ℤ} (f : P ⟶ Q) (q : ℤ)
    (hz : HomologicalComplex.homologyMap f q = 0)
    (tC : IsPowTorsion J ((Cone.cone f).homology (q - 1))) :
    lam.len (P.homology q) ≤ lam.len ((Cone.cone f).homology (q - 1)) := by
  have hrel : q - 1 + 1 = q := by omega
  have : Epi (Cone.δ f (q - 1) q hrel) := (Cone.exact₁ f (q - 1) q hrel).epi_f hz
  exact lam.len_le_of_surjective (Cone.δ f (q - 1) q hrel).hom
    ((ModuleCat.epi_iff_surjective _).mp inferInstance) tC

/-- 錐の冪ねじれ性は、零作用による単射から右のホモロジーへ移る。 -/
theorem isPowTorsion_of_cone_of_homologyMap_eq_zero
    {P Q : CochainComplex (ModuleCat.{u} R) ℤ} (f : P ⟶ Q) (q : ℤ)
    (hz : HomologicalComplex.homologyMap f q = 0)
    (tC : IsPowTorsion J ((Cone.cone f).homology q)) : IsPowTorsion J (Q.homology q) := by
  have : Mono (HomologicalComplex.homologyMap (CochainComplex.mappingCone.inr f) q) :=
    (Cone.exact₂ f q).mono_g hz
  exact IsPowTorsion.of_injective
    (HomologicalComplex.homologyMap (CochainComplex.mappingCone.inr f) q).hom
    ((ModuleCat.mono_iff_injective _).mp inferInstance) tC

end SerrePositivity
