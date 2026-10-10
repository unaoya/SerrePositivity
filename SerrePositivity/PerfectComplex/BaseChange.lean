module

public import SerrePositivity.PerfectComplex.HomotopyCategory
public import SerrePositivity.PerfectComplex.Closure

/-! # 有限射影ホモトピー圏の係数変更

任意の環準同型による係数変更と、その合成の自然同型を構成する。
-/

@[expose] public section

universe u

namespace SerrePositivity

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits

variable {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)

/-- 有限射影性は係数変更で保たれる。 -/
lemma projective_baseChange (M : ModuleCat.{u} R) [Module.Projective R M] :
    Module.Projective S ((ModuleCat.extendScalars.{u, u, u} φ).obj M) := by
  let := φ.toAlgebra
  change Module.Projective S (TensorProduct R S M)
  infer_instance

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
