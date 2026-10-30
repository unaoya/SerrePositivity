module
public import SerrePositivity.CategoryTheory.HomotopyProperty

public import SerrePositivity.CategoryTheory.BoundedHomotopy
public import SerrePositivity.CategoryTheory.ScalarSupport
public import SerrePositivity.CategoryTheory.Triangulated.VerdierLift
public import SerrePositivity.PerfectComplex.Support

/-! # 有界有限射影複体の支持つきホモトピー圏

任意の可換環上で有限射影項を用いる。自由加群への置換や局所環の仮定は使わない。
-/

@[expose] public section

universe u

namespace SerrePositivity

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ZeroObject

variable (R : Type u) [CommRing R]

/-- 項が有限射影で、有限個の次数の外で零となる複体。 -/
def strictlyPerfectComplex : ObjectProperty (CochainComplex (ModuleCat.{u} R) ℤ) :=
  fun P ↦ strictlyBoundedComplex (ModuleCat R) P ∧
    ∀ q, Module.Finite R (P.X q) ∧ Module.Projective R (P.X q)

/-- 有界有限射影複体を代表とするホモトピー圏の対象。 -/
def perfectHomotopyProperty : ObjectProperty (HomotopyCategory (ModuleCat.{u} R) (.up ℤ)) :=
  (strictlyPerfectComplex R).strictMap (HomotopyCategory.quotient _ _)

@[simp] lemma perfectHomotopyProperty_quotient (P : CochainComplex (ModuleCat.{u} R) ℤ) :
    perfectHomotopyProperty R ((HomotopyCategory.quotient _ _).obj P) ↔
      strictlyPerfectComplex R P :=
  homotopyProperty_strictMap_quotient (strictlyPerfectComplex R) P

section
variable {R}

/-- The zero complex is strictly perfect over every commutative ring. -/
lemma strictlyPerfectComplex_zero :
    strictlyPerfectComplex R (0 : CochainComplex (ModuleCat.{u} R) ℤ) := by
  refine ⟨⟨0, 0, inferInstance, inferInstance⟩, fun i ↦ ?_⟩
  have hz : IsZero ((0 : CochainComplex (ModuleCat.{u} R) ℤ).X i) :=
    (HomologicalComplex.eval _ _ i).map_isZero
      (isZero_zero (CochainComplex (ModuleCat.{u} R) ℤ))
  have : Module.Free R ((0 : CochainComplex (ModuleCat.{u} R) ℤ).X i) :=
    isZero_moduleCat_free hz
  exact ⟨isZero_moduleCat_finite hz, Module.Projective.of_free⟩

/-- Integer shifts preserve strict perfectness. -/
lemma strictlyPerfectComplex_shift {P : CochainComplex (ModuleCat.{u} R) ℤ}
    (hp : strictlyPerfectComplex R P) (n : ℤ) : strictlyPerfectComplex R (P⟦n⟧) := by
  exact ⟨strictlyBoundedComplex_shift _ hp.1 n, fun i ↦ hp.2 (i + n)⟩

end

instance : (perfectHomotopyProperty R).ContainsZero where
  exists_zero := ⟨(HomotopyCategory.quotient _ _).obj 0,
    Functor.map_isZero _ (isZero_zero _), by
      rw [perfectHomotopyProperty_quotient]
      exact strictlyPerfectComplex_zero⟩

instance : (perfectHomotopyProperty R).IsStableUnderShift ℤ where
  isStableUnderShiftBy n :=
    { le_shift X hX := by
        obtain ⟨P : CochainComplex _ _, rfl⟩ := X.quotient_obj_surjective
        rw [perfectHomotopyProperty_quotient] at hX
        rw [ObjectProperty.prop_shift_iff, HomotopyCategory.shift_quotient_obj,
          perfectHomotopyProperty_quotient]
        exact strictlyPerfectComplex_shift hX n }

/-- 有限射影複体の写像錐は有限射影複体である。 -/
lemma strictlyPerfectComplex_mappingCone {P Q : CochainComplex (ModuleCat.{u} R) ℤ}
    (f : P ⟶ Q) (hP : strictlyPerfectComplex R P) (hQ : strictlyPerfectComplex R Q) :
    strictlyPerfectComplex R (CochainComplex.mappingCone f) := by
  refine ⟨strictlyBoundedComplex_mappingCone _ f hP.1 hQ.1, fun q ↦ ?_⟩
  have := (hP.2 (q + 1)).1
  have := (hP.2 (q + 1)).2
  have := (hQ.2 q).1
  have := (hQ.2 q).2
  let e := (HomologicalComplex.homotopyCofiber.XIsoBiprod f q (q + 1) rfl ≪≫
    ModuleCat.biprodIsoProd _ _).toLinearEquiv
  exact ⟨Module.Finite.equiv e.symm, Module.Projective.of_equiv' e.symm⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
instance : (perfectHomotopyProperty R).IsTriangulatedClosed₃ :=
  homotopyProperty_isTriangulatedClosed₃ _ _ (perfectHomotopyProperty_quotient R)
    (fun f => strictlyPerfectComplex_mappingCone R f)

instance : (perfectHomotopyProperty R).IsTriangulated where
  toIsTriangulatedClosed₂ := .of_isTriangulatedClosed₃

/-- 有界有限射影複体のホモトピー圏。 -/
abbrev PerfectHomotopy := (perfectHomotopyProperty R).FullSubcategory

/-- 全ホモトピー圏への三角関手。 -/
abbrev perfectHomotopyInclusion : PerfectHomotopy R ⥤
    HomotopyCategory (ModuleCat.{u} R) (.up ℤ) := (perfectHomotopyProperty R).ι

/-- 具体的な有限射影複体をホモトピー圏の対象とする。 -/
def perfectHomotopyObj (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (hP : strictlyPerfectComplex R P) : PerfectHomotopy R :=
  ⟨(HomotopyCategory.quotient _ _).obj P, (perfectHomotopyProperty_quotient R P).mpr hP⟩

variable {R} {e : ℕ} (z : Fin e → R)

/-- 指定したスカラーで支持される有界有限射影複体の三角圏。 -/
abbrev SupportedPerfectHomotopy :=
  (scalarSupported (C := PerfectHomotopy R) z).FullSubcategory

/-- 台の条件を忘れる三角関手。 -/
abbrev supportedPerfectInclusion : SupportedPerfectHomotopy z ⥤ PerfectHomotopy R :=
  (scalarSupported (C := PerfectHomotopy R) z).ι

/-- 具体的な複体の台と、ホモトピー圏におけるスカラーの零作用の一致。 -/
lemma perfectHomotopyObj_supported_iff (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (hP : strictlyPerfectComplex R P) :
    scalarSupported z (perfectHomotopyObj R P hP) ↔ IsSupported z P := by
  rw [isSupported_iff]
  constructor
  · rintro ⟨v, hv, h⟩
    exact ⟨v, fun j ↦ congrArg (perfectHomotopyInclusion R).map (h j)⟩
  · intro h
    obtain ⟨v, hv, h⟩ := ((isSupported_iff z P).mpr h).exists_pos
    refine ⟨v, hv, fun j ↦ (perfectHomotopyInclusion R).map_injective ?_⟩
    exact (nonempty_homotopy_smul_id_zero_iff _ P).mp (h j)

/-- 任意の可換環の有界有限射影複体では、抽象的な零作用による支持条件は
ホモロジーの幾何学的支持条件に一致する。 -/
lemma perfectHomotopyObj_supported_iff_homologySupport
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (hP : strictlyPerfectComplex R P) :
    scalarSupported z (perfectHomotopyObj R P hP) ↔
      HasHomologySupport (Ideal.span (Set.range z)) P := by
  rw [perfectHomotopyObj_supported_iff]
  apply isSupported_iff_homologySupport z P (fun q ↦ (hP.2 q).1)
    (fun q ↦ ?_)
  · obtain ⟨a, b, ha, hb⟩ := hP.1
    exact ⟨a, b, fun q hq ↦ hq.elim (fun h ↦ P.isZero_of_isStrictlyGE a q h)
      (fun h ↦ P.isZero_of_isStrictlyLE b q h)⟩
  · have := (hP.2 q).2
    infer_instance

/-- perfect ホモトピー圏の全対象について、支持部分圏を実際のホモロジーの台で判定する。 -/
lemma perfectHomotopy_supported_iff_homologySupport (X : PerfectHomotopy R) :
    scalarSupported z X ↔ ∀ q : ℤ,
      Module.support R ((HomotopyCategory.homologyFunctor (ModuleCat.{u} R) (.up ℤ) q).obj
        X.obj) ⊆ PrimeSpectrum.zeroLocus (Ideal.span (Set.range z)) := by
  obtain ⟨X, hX⟩ := X
  obtain ⟨P : CochainComplex _ _, rfl⟩ := X.quotient_obj_surjective
  have hP := (perfectHomotopyProperty_quotient R P).mp hX
  change scalarSupported z (perfectHomotopyObj R P hP) ↔ _
  rw [perfectHomotopyObj_supported_iff_homologySupport]
  unfold HasHomologySupport
  apply forall_congr'
  intro q
  exact (congrArg (fun s : Set (PrimeSpectrum R) ↦
    s ⊆ PrimeSpectrum.zeroLocus (Ideal.span (Set.range z)))
    (((HomotopyCategory.homologyFunctorFactors _ _ q).app P).toLinearEquiv.support_eq)).symm.to_iff

end SerrePositivity
