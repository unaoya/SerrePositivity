module
public import SerrePositivity.DifferentialGraded.Perfect.RingTopTruncation
public import SerrePositivity.HomologicalAlgebra.Complex.ConeLES

/-! # 有限射影singleによる上端被覆のconeを一段短くする

次数幅の帰納法で用いる、実際の有限射影複体上の操作。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits HomologicalComplex
variable (A : Type u) [CommRing A]

lemma ringComplex_coverCone_topExact {F P : Complex A} (f : F ⟶ P) (b : ℤ)
    [Epi (homologyMap f b)] (hF : IsZero (F.homology (b + 1))) :
    (CochainComplex.mappingCone f).ExactAt b := by
  have hg : homologyMap (CochainComplex.mappingCone.inr f) b = 0 :=
    (Cone.exact₂ f b).epi_f_iff.1 inferInstance
  have : Mono (Cone.δ f b (b + 1) rfl) := (Cone.exact₃ f b (b + 1) rfl).mono_g hg
  rw [exactAt_iff_isZero_homology, IsZero.iff_id_eq_zero]
  apply (cancel_mono (Cone.δ f b (b + 1) rfl)).1
  exact hF.eq_of_tgt _ _

lemma ringSingleCone_strictlyLE (F : ModuleCat.{u} A) (P : Complex A) (b : ℤ)
    (f : (single (ModuleCat.{u} A) (.up ℤ) b).obj F ⟶ P) [P.IsStrictlyLE b] :
    (CochainComplex.mappingCone f).IsStrictlyLE b := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  rw [CochainComplex.mappingCone.isZero_X_iff]
  exact ⟨isZero_single_obj_X (.up ℤ) b F (i + 1) (by omega),
    P.isZero_of_isStrictlyLE b i hi⟩

lemma ringSingleCone_strictlyGE (F : ModuleCat.{u} A) (P : Complex A) (a b : ℤ)
    (f : (single (ModuleCat.{u} A) (.up ℤ) b).obj F ⟶ P)
    [P.IsStrictlyGE a] (hab : a < b) : (CochainComplex.mappingCone f).IsStrictlyGE a :=
  CochainComplex.isStrictlyGE_mappingCone f b a a hab (le_refl _)

lemma ringSingleCoverCone_topTruncation (F : ModuleCat.{u} A)
    [Module.Finite A F] [Module.Projective A F]
    (P : Complex A) (hP : strictlyPerfectComplex A P) (b : ℤ)
    (f : (single (ModuleCat.{u} A) (.up ℤ) b).obj F ⟶ P)
    [P.IsStrictlyLE b] [Epi (homologyMap f b)] :
    strictlyPerfectComplex A ((CochainComplex.mappingCone f).truncLE (b - 1)) ∧
      QuasiIso ((CochainComplex.mappingCone f).ιTruncLE (b - 1)) := by
  have hC := strictlyPerfectComplex_mappingCone A f (strictlyPerfectComplex_single A F b) hP
  have htop := ringComplex_coverCone_topExact A f b
    (isZero_single_obj_homology (.up ℤ) b F (b + 1) (by omega))
  have : (CochainComplex.mappingCone f).IsStrictlyLE ((b - 1) + 1) := by
    simpa only [sub_add_cancel] using ringSingleCone_strictlyLE A F P b f
  exact ringComplex_topTruncation A _ hC (b - 1) (by simpa only [sub_add_cancel] using htop)

lemma ringSingleCoverCone_shorterModel (F : ModuleCat.{u} A)
    [Module.Finite A F] [Module.Projective A F]
    (P : Complex A) (hP : strictlyPerfectComplex A P) (a b : ℤ)
    (f : (single (ModuleCat.{u} A) (.up ℤ) b).obj F ⟶ P)
    [P.IsStrictlyGE a] [P.IsStrictlyLE b] [Epi (homologyMap f b)] (hab : a < b) :
    ∃ Q : Complex A, strictlyPerfectComplex A Q ∧ Q.IsStrictlyGE a ∧ Q.IsStrictlyLE (b - 1) ∧
      ∃ i : Q ⟶ CochainComplex.mappingCone f, QuasiIso i := by
  obtain ⟨hQ, hi⟩ := ringSingleCoverCone_topTruncation A F P hP b f
  have : (CochainComplex.mappingCone f).IsStrictlyGE a :=
    ringSingleCone_strictlyGE A F P a b f hab
  have hge := ringComplex_truncLE_strictlyGE A (CochainComplex.mappingCone f) a (b - 1)
    (by omega)
  exact ⟨_, hQ, hge, inferInstance, _, hi⟩

end SerrePositivity.DifferentialGraded
