module

public import SerrePositivity.CategoryTheory.HomotopyProperty
public import SerrePositivity.CategoryTheory.BoundedHomotopy
public import SerrePositivity.CategoryTheory.ScalarSupport
public import SerrePositivity.CategoryTheory.Triangulated.VerdierLift
public import SerrePositivity.PerfectComplex.Free.Support
public import SerrePositivity.HomologicalAlgebra.ProjectiveBaseChange
public import SerrePositivity.PerfectComplex.Free.K0
public import SerrePositivity.HomologicalAlgebra.CochainTensor.ShortExact

/-! # 有界有限射影複体の台つきホモトピー圏

## 概要

任意の可換環上の有界な有限射影複体の、台つきホモトピー圏を作り、任意の環準同型による係数変更とその合成の自然同型を与える。次数ごとの引き込み（鎖写像でなくてよい）の完全性も示す。

## 方針

有限射影の項を使い、自由加群への置き換えや局所環の仮定は使わない。

## 規約

K 射影性と擬同型の判定は Mathlib の `isKProjective_of_projective`・`IsKProjective.quasiIso_iff` の包み（利用が多いので残す）。

## 使われ方

`Perfect/FreeComparison`・`ClosedSupport/*`、KTheory。
-/

@[expose] public noncomputable section

universe u

section HomotopyCategoryPart

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

end HomotopyCategoryPart

section BaseChangePart

namespace SerrePositivity

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits

variable {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)

/-- 厳密な有界性と各項の有限射影性は係数変更で保たれる。 -/
lemma strictlyPerfectComplex_baseChange (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (hP : strictlyPerfectComplex R P) : strictlyPerfectComplex S (baseChange φ P) := by
  refine ⟨?_, fun q ↦ ?_⟩
  · obtain ⟨a, b, ha, hb⟩ := hP.1
    exact ⟨a, b, inferInstance, inferInstance⟩
  · have := (hP.2 q).1
    have := (hP.2 q).2
    exact ⟨finite_baseChange φ (P.X q), projective_baseChange φ (P.X q)⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- 有限射影ホモトピー圏の係数変更。 -/
noncomputable def perfectChangeRing : PerfectHomotopy R ⥤ PerfectHomotopy S :=
  (perfectHomotopyProperty S).lift
    (perfectHomotopyInclusion R ⋙ (ModuleCat.extendScalars φ).mapHomotopyCategory (.up ℤ))
    (by
      rintro ⟨X, hX⟩
      obtain ⟨P : CochainComplex _ _, rfl⟩ := X.quotient_obj_surjective
      exact (perfectHomotopyProperty_quotient S (baseChange φ P)).mpr
        (strictlyPerfectComplex_baseChange φ P ((perfectHomotopyProperty_quotient R P).mp hX)))

noncomputable instance : (perfectChangeRing φ).CommShift ℤ := by
  dsimp only [perfectChangeRing]
  infer_instance

instance : (perfectChangeRing φ).IsTriangulated := by
  dsimp only [perfectChangeRing]
  infer_instance

variable {e : ℕ} (z : Fin e → R)

include φ in
/-- 係数変更関手はスカラーによる支持条件を保つ。 -/
lemma perfectChangeRing_supported (X : PerfectHomotopy R) (hX : scalarSupported z X) :
    scalarSupported (φ ∘ z) ((perfectChangeRing φ).obj X) := by
  obtain ⟨X, hP⟩ := X
  obtain ⟨P : CochainComplex _ _, rfl⟩ := X.quotient_obj_surjective
  have hp := (perfectHomotopyProperty_quotient R P).mp hP
  exact (perfectHomotopyObj_supported_iff (φ ∘ z) (baseChange φ P)
    (strictlyPerfectComplex_baseChange φ P hp)).mpr
      (isSupported_baseChange φ ((perfectHomotopyObj_supported_iff z P hp).mp hX))

/-- 支持つき有限射影ホモトピー圏の係数変更。 -/
noncomputable def supportedPerfectChangeRing :
    SupportedPerfectHomotopy z ⥤ SupportedPerfectHomotopy (φ ∘ z) :=
  (scalarSupported (C := PerfectHomotopy S) (φ ∘ z)).lift
    (supportedPerfectInclusion z ⋙ perfectChangeRing φ)
    (fun X ↦ perfectChangeRing_supported φ z X.obj X.property)

noncomputable instance : (supportedPerfectChangeRing φ z).CommShift ℤ := by
  dsimp only [supportedPerfectChangeRing]
  infer_instance

instance : (supportedPerfectChangeRing φ z).IsTriangulated := by
  dsimp only [supportedPerfectChangeRing]
  infer_instance

variable {T : Type u} [CommRing T] (ψ : S →+* T)

/-- 二段階の係数変更と直接の係数変更の自然同型。 -/
noncomputable def perfectChangeRingCompIso :
    perfectChangeRing φ ⋙ perfectChangeRing ψ ≅ perfectChangeRing (ψ.comp φ) := by
  let i := Functor.mapHomotopyCategoryCompIso (ModuleCat.extendScalarsComp φ ψ).symm (.up ℤ)
  exact NatIso.ofComponents (fun X ↦ ObjectProperty.isoMk _ (i.app X.obj)) (fun f ↦ by
    apply ObjectProperty.hom_ext
    exact i.hom.naturality f.hom)

/-- 二段階の係数変更の比較は支持つき部分圏に制限できる。 -/
noncomputable def supportedPerfectChangeRingCompIso :
    supportedPerfectChangeRing φ z ⋙ supportedPerfectChangeRing ψ (φ ∘ z) ≅
      supportedPerfectChangeRing (ψ.comp φ) z :=
  NatIso.ofComponents
    (fun X ↦ ObjectProperty.isoMk _ ((perfectChangeRingCompIso φ ψ).app X.obj))
    (fun f ↦ by
      apply ObjectProperty.hom_ext
      exact (perfectChangeRingCompIso φ ψ).hom.naturality f.hom)

end SerrePositivity

end BaseChangePart

section DegreewiseRetractPart

set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity
open CategoryTheory Category Limits
variable {R : Type u} [CommRing R]

lemma strictlyPerfectComplex_of_degreewiseRetract
    {K L : CochainComplex (ModuleCat.{u} R) ℤ} (i : K ⟶ L)
    (r : ∀ n, L.X n ⟶ K.X n) (hr : ∀ n, i.f n ≫ r n = 𝟙 (K.X n))
    (hL : strictlyPerfectComplex R L) : strictlyPerfectComplex R K := by
  have hz : ∀ n, IsZero (L.X n) → IsZero (K.X n) := by
    intro n hn
    rw [IsZero.iff_id_eq_zero, ← hr n, hn.eq_of_tgt (i.f n) 0, zero_comp]
  obtain ⟨a, b, ha, hb⟩ := hL.1
  refine ⟨⟨a, b, ?_, ?_⟩, fun n => ?_⟩
  · exact (K.isStrictlyGE_iff a).mpr fun n hn => hz n (L.isZero_of_isStrictlyGE a n hn)
  · exact (K.isStrictlyLE_iff b).mpr fun n hn => hz n (L.isZero_of_isStrictlyLE b n hn)
  · have := (hL.2 n).1
    have := (hL.2 n).2
    have hs : Function.Surjective (r n).hom := by
      intro x
      exact ⟨(i.f n).hom x, congrArg (fun f => f.hom x) (hr n)⟩
    exact ⟨Module.Finite.of_surjective (r n).hom hs,
      Module.Projective.of_split (i.f n).hom (r n).hom (congrArg (fun f => f.hom) (hr n))⟩

/-- A short exact sequence with projective quotient terms makes the first complex
a degreewise retract of the middle complex. -/
lemma strictlyPerfectComplex_of_shortExact
    (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ)) (hS : S.ShortExact)
    (h₂ : strictlyPerfectComplex R S.X₂) (h₃ : ∀ i, Module.Projective R (S.X₃.X i)) :
    strictlyPerfectComplex R S.X₁ := by
  let σ := cochainDegreewiseSplittingOfProjective S hS h₃
  exact strictlyPerfectComplex_of_degreewiseRetract S.f
    (cochainSplittingRetraction S σ) (fun n => (σ n).f_r) h₂

end SerrePositivity

end DegreewiseRetractPart
