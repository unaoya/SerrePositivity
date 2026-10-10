module

public import SerrePositivity.PerfectComplex.HomotopyCategory
public import SerrePositivity.LengthAlgebra.Koszul
public import SerrePositivity.CategoryTheory.HomologicalEuler
public import Mathlib.Algebra.Homology.HomotopyCategory.HomologicalFunctor
public import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence

/-! # 有限射影複体のホモロジー評価

ホモロジーを取ってから有限長さの Serre 商へ送る。
この実際のホモロジー関手から共通の Euler 評価を構成する。
-/

@[expose] public section

universe u

namespace SerrePositivity.LengthAlgebra

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

variable {R : Type u} [CommRing R] {J : Ideal R} (lam : NormalizedLength R J)
  (hfg : J.FG) {e : ℕ} (z : Fin e → R)
  (hJ : J ≤ (Ideal.span (Set.range z)).radical) (hfin : KoszulFinite lam z)

/-- 支持つき有限射影複体の通常のホモロジー関手。 -/
noncomputable abbrev perfectModuleHomology (q : ℤ) :
    SupportedPerfectHomotopy z ⥤ ModuleCat.{u} R :=
  supportedPerfectInclusion z ⋙ perfectHomotopyInclusion R ⋙
    HomotopyCategory.homologyFunctor _ _ q

include hfg hJ hfin in
/-- 支持と Koszul 有限性によって、評価先を有限長さの冪ねじれ加群に制限できる。 -/
lemma perfectModuleHomology_mem (X : SupportedPerfectHomotopy z) (q : ℤ) :
    finiteLengthTorsion lam ((perfectModuleHomology z q).obj X) := by
  obtain ⟨⟨X, hX⟩, hz⟩ := X
  obtain ⟨P : CochainComplex _ _, rfl⟩ := X.quotient_obj_surjective
  have hP := (perfectHomotopyProperty_quotient R P).mp hX
  have hs : IsSupported z P := (perfectHomotopyObj_supported_iff z P hP).mp hz
  apply (finiteLengthTorsion lam).prop_of_iso
    ((HomotopyCategory.homologyFunctorFactors _ _ q).app P).symm
  apply homology_mem_finiteLengthTorsion lam z hfg hJ hfin P
    (fun q ↦ (hP.2 q).1) (fun q ↦ (hP.2 q).2) _ hs q
  obtain ⟨a, b, ha, hb⟩ := hP.1
  exact ⟨a, b, fun q hq ↦ hq.elim (fun h ↦ P.isZero_of_isStrictlyGE a q h)
    (fun h ↦ P.isZero_of_isStrictlyLE b q h)⟩

/-- 有限長さの冪ねじれ加群に値をもつホモロジー関手。 -/
noncomputable def perfectFiniteHomology (q : ℤ) :
    SupportedPerfectHomotopy z ⥤ FiniteLengthTorsion lam :=
  (finiteLengthTorsion lam).lift (perfectModuleHomology z q)
    (fun X ↦ perfectModuleHomology_mem lam hfg z hJ hfin X q)

instance perfectFiniteHomology_additive (q : ℤ) :
    (perfectFiniteHomology lam hfg z hJ hfin q).Additive := by
  dsimp only [perfectFiniteHomology]
  infer_instance

instance perfectFiniteHomology_isHomological (q : ℤ) :
    (perfectFiniteHomology lam hfg z hJ hfin q).IsHomological where
  exact T hT := by
    apply (ShortComplex.exact_map_iff_of_faithful _ (finiteLengthTorsion lam).ι).mp
    exact (perfectModuleHomology z q).map_distinguished_exact T hT

/-- 有限長さの商に値をもつホモロジー関手。 -/
noncomputable def perfectQuotientHomology (q : ℤ) :
    SupportedPerfectHomotopy z ⥤ FiniteLengthQuotient lam :=
  perfectFiniteHomology lam hfg z hJ hfin q ⋙ finiteLengthQuotientFunctor lam

instance perfectQuotientHomology_additive (q : ℤ) :
    (perfectQuotientHomology lam hfg z hJ hfin q).Additive := by
  dsimp only [perfectQuotientHomology]
  infer_instance

instance perfectQuotientHomology_isHomological (q : ℤ) :
    (perfectQuotientHomology lam hfg z hJ hfin q).IsHomological where
  exact T hT :=
    ((perfectFiniteHomology lam hfg z hJ hfin q).map_distinguished_exact T hT).map
      (finiteLengthQuotientFunctor lam)

/-- 第零次関手のシフトと、各次数のホモロジーの自然同型。 -/
noncomputable def perfectQuotientHomologyShiftIso (q : ℤ) :
    shiftFunctor _ q ⋙ perfectQuotientHomology lam hfg z hJ hfin 0 ≅
      perfectQuotientHomology lam hfg z hJ hfin q := by
  let G := supportedPerfectInclusion z ⋙ perfectHomotopyInclusion R
  let H := HomotopyCategory.homologyFunctor (ModuleCat.{u} R) (.up ℤ) 0
  let i : shiftFunctor _ q ⋙ perfectModuleHomology z 0 ≅ perfectModuleHomology z q :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (G.commShiftIso q) H ≪≫ Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft G (H.isoShift q)
  let j : shiftFunctor _ q ⋙ perfectFiniteHomology lam hfg z hJ hfin 0 ≅
      perfectFiniteHomology lam hfg z hJ hfin q :=
    NatIso.ofComponents (fun X ↦ ObjectProperty.isoMk _ (i.app X)) (fun f ↦ by
      apply ObjectProperty.hom_ext
      exact i.hom.naturality f)
  exact Functor.isoWhiskerRight j (finiteLengthQuotientFunctor lam)

/-- 各対象ごとの有界性。圏全体に共通の振幅は要求しない。 -/
lemma perfectQuotientHomology_bounded (X : SupportedPerfectHomotopy z) :
    ∃ a b : ℤ, ∀ q, q < a ∨ b < q →
      IsZero ((perfectQuotientHomology lam hfg z hJ hfin q).obj X) := by
  obtain ⟨⟨X, hX⟩, hz⟩ := X
  obtain ⟨P : CochainComplex _ _, rfl⟩ := X.quotient_obj_surjective
  obtain ⟨⟨a, b, ha, hb⟩, hp⟩ := (perfectHomotopyProperty_quotient R P).mp hX
  refine ⟨a, b, fun q hq ↦ ?_⟩
  apply (finiteLengthQuotientFunctor lam).map_isZero
  rw [IsZero.iff_id_eq_zero]
  apply ObjectProperty.hom_ext
  exact ((isZero_homology_of_isZero_X P q
    (hq.elim (fun h ↦ P.isZero_of_isStrictlyGE a q h)
      (fun h ↦ P.isZero_of_isStrictlyLE b q h))).of_iso
      ((HomotopyCategory.homologyFunctorFactors _ _ q).app P)).eq_of_src _ _

noncomputable instance perfectQuotientHomology_shiftSequence :
    (perfectQuotientHomology lam hfg z hJ hfin 0).ShiftSequence ℤ :=
  Functor.ShiftSequence.tautological _ ℤ

/-- 共通 Euler 評価に渡すシフト列の有界性。 -/
lemma perfectQuotientHomology_shift_bounded (X : SupportedPerfectHomotopy z) :
    ∃ a b : ℤ, ∀ q, q < a ∨ b < q →
      IsZero (((perfectQuotientHomology lam hfg z hJ hfin 0).shift q).obj X) := by
  obtain ⟨a, b, hab⟩ := perfectQuotientHomology_bounded lam hfg z hJ hfin X
  exact ⟨a, b, fun q hq ↦ (hab q hq).of_iso
    ((perfectQuotientHomologyShiftIso lam hfg z hJ hfin q).app X)⟩

/-- 有限射影版の Euler 評価は共通のホモロジー的 Euler 評価で定義する。 -/
noncomputable def perfectEuler (X : SupportedPerfectHomotopy z) : ℝ :=
  homologicalEuler (quotientLength lam) (perfectQuotientHomology lam hfg z hJ hfin 0) X

/-- 共通の三角加法性により得られる Euler 準同型。 -/
noncomputable def perfectEulerK0 : TriangulatedK0 (SupportedPerfectHomotopy z) →+ ℝ :=
  homologicalEulerK0 (quotientLength lam) (quotientLength_iso lam) (quotientLength_add lam)
    (perfectQuotientHomology lam hfg z hJ hfin 0)
    (fun X hX ↦ (quotientLength_eq_zero_iff lam X).mpr hX)
    (perfectQuotientHomology_shift_bounded lam hfg z hJ hfin)

@[simp] lemma perfectEulerK0_mk (X : SupportedPerfectHomotopy z) :
    perfectEulerK0 lam hfg z hJ hfin (TriangulatedK0.mk X) =
      perfectEuler lam hfg z hJ hfin X := homologicalEulerK0_mk ..

/-- 代表複体上で、新しい評価は従来のホモロジーの交代和と一致する。 -/
lemma perfectEuler_eq_lambdaEuler (X : SupportedPerfectHomotopy z) :
    perfectEuler lam hfg z hJ hfin X = lambdaEuler lam X.obj.obj.as := by
  unfold perfectEuler homologicalEuler lambdaEuler
  congr 1
  funext q
  congr 1
  refine (quotientLength_iso lam
    ((perfectQuotientHomologyShiftIso lam hfg z hJ hfin q).app X)).trans ?_
  exact congrArg ENNReal.toReal (lam.len_congr _ _
    ((HomotopyCategory.homologyFunctorFactors _ _ q).app X.obj.obj.as).toLinearEquiv)

/-- 有限射影版の三角加法性は、共通の Euler 加法性の適用である。 -/
lemma perfectEuler_triangle (T : Triangle (SupportedPerfectHomotopy z))
    (hT : T ∈ distTriang _) :
    perfectEuler lam hfg z hJ hfin T.obj₂ =
      perfectEuler lam hfg z hJ hfin T.obj₁ + perfectEuler lam hfg z hJ hfin T.obj₃ :=
  homologicalEuler_triangle (quotientLength lam) (quotientLength_iso lam)
    (quotientLength_add lam) (perfectQuotientHomology lam hfg z hJ hfin 0)
    (fun X hX ↦ (quotientLength_eq_zero_iff lam X).mpr hX)
    (perfectQuotientHomology_shift_bounded lam hfg z hJ hfin) T hT

end SerrePositivity.LengthAlgebra
