module

public import SerrePositivity.PerfectComplex.ClosedSupportFunctoriality
public import SerrePositivity.HomologicalAlgebra.KProjectiveLift
public import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact

/-! # 閉集合版 K₀ の擬同型・短完全列・錐の関係

有界有限射影複体は K-projective なので、擬同型はホモトピー同値である。
短完全列の商は単射の錐と擬同型になり、K₀ の加法関係が一致する。
-/

@[expose] public section

noncomputable section

universe u

namespace SerrePositivity

open CategoryTheory Limits Pretriangulated
open scoped ZeroObject

variable {R : Type u} [CommRing R]

/-- A bounded complex of finite projective modules is K-projective. -/
lemma strictlyPerfectComplex_isKProjective
    {P : CochainComplex (ModuleCat.{u} R) ℤ} (hp : strictlyPerfectComplex R P) :
    P.IsKProjective := by
  obtain ⟨a, b, ha, hb⟩ := hp.1
  have : ∀ i, Projective (P.X i) := fun i ↦ by
    have := (hp.2 i).2
    infer_instance
  exact CochainComplex.isKProjective_of_projective P b

/-- For strictly perfect complexes, quasi-isomorphisms and homotopy equivalences agree. -/
lemma strictlyPerfectComplex_quasiIso_iff
    {P Q : CochainComplex (ModuleCat.{u} R) ℤ}
    (hp : strictlyPerfectComplex R P) (hq : strictlyPerfectComplex R Q) (f : P ⟶ Q) :
    QuasiIso f ↔ HomologicalComplex.homotopyEquivalences (ModuleCat.{u} R) (.up ℤ) f := by
  have := strictlyPerfectComplex_isKProjective hp
  have := strictlyPerfectComplex_isKProjective hq
  exact CochainComplex.IsKProjective.quasiIso_iff f

variable (Z : TopologicalSpace.Closeds (PrimeSpectrum R))
  (P Q : CochainComplex (ModuleCat.{u} R) ℤ)
  (hp : strictlyPerfectComplex R P) (hq : strictlyPerfectComplex R Q)
  (hsP : HasHomologySupportOn Z P) (hsQ : HasHomologySupportOn Z Q)

/-- The cone of a supported perfect short exact sequence represents its third term. -/
def supportedPerfectOnConeIsoOfShortExact
    (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ)) (hS : S.ShortExact)
    (h₁ : strictlyPerfectComplex R S.X₁) (h₂ : strictlyPerfectComplex R S.X₂)
    (h₃ : strictlyPerfectComplex R S.X₃)
    (s₁ : HasHomologySupportOn Z S.X₁) (s₂ : HasHomologySupportOn Z S.X₂)
    (s₃ : HasHomologySupportOn Z S.X₃) :
    supportedPerfectOnObj Z (CochainComplex.mappingCone S.f)
      (strictlyPerfectComplex_mappingCone R S.f h₁ h₂) (s₁.mappingCone S.f s₂) ≅
        supportedPerfectOnObj Z S.X₃ h₃ s₃ :=
  let e := Classical.choose ((strictlyPerfectComplex_quasiIso_iff
    (strictlyPerfectComplex_mappingCone R S.f h₁ h₂) h₃
    (CochainComplex.mappingCone.descShortComplex S)).mp
      (CochainComplex.mappingCone.quasiIso_descShortComplex hS))
  ObjectProperty.isoMk _ (ObjectProperty.isoMk _ (HomotopyCategory.isoOfHomotopyEquiv e))

/-- The concrete cone triangle lifted to the closed-support category. -/
def supportedPerfectOnConeTriangle (f : P ⟶ Q) : Triangle (SupportedPerfectHomotopyOn Z) :=
  Triangle.mk
    (ObjectProperty.homMk (ObjectProperty.homMk ((homotopyQuot R).map f)))
    (ObjectProperty.homMk (ObjectProperty.homMk
      ((CochainComplex.mappingCone.triangleh f).mor₂)))
    (ObjectProperty.homMk (ObjectProperty.homMk
      ((CochainComplex.mappingCone.triangleh f).mor₃ ≫
        ((supportedPerfectOnInclusion Z ⋙ perfectHomotopyInclusion R).commShiftIso
          (1 : ℤ)).inv.app (supportedPerfectOnObj Z P hp hsP))))
    (X := supportedPerfectOnObj Z P hp hsP)
    (Y := supportedPerfectOnObj Z Q hq hsQ)
    (Z := supportedPerfectOnObj Z (CochainComplex.mappingCone f)
      (strictlyPerfectComplex_mappingCone R f hp hq) (hsP.mappingCone f hsQ))

set_option backward.isDefEq.respectTransparency false in
lemma supportedPerfectOnConeTriangle_distinguished (f : P ⟶ Q) :
    supportedPerfectOnConeTriangle Z P Q hp hq hsP hsQ f ∈ distTriang _ := by
  change (perfectHomotopyInclusion R).mapTriangle.obj
    ((supportedPerfectOnInclusion Z).mapTriangle.obj
      (supportedPerfectOnConeTriangle Z P Q hp hq hsP hsQ f)) ∈ distTriang _
  convert HomotopyCategory.mappingCone_triangleh_distinguished f using 1
  · simp [supportedPerfectOnConeTriangle, Functor.mapTriangle,
      Functor.commShiftIso_comp_inv_app, Category.assoc, supportedPerfectOnObj,
      perfectHomotopyObj, homotopyQuot, CochainComplex.mappingCone.triangle]

/-- The canonical short exact sequence `Q → Cone(f) → P[1]`. -/
def closedSupportConeShortComplex (f : P ⟶ Q) :
    ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ) :=
  ShortComplex.mk (CochainComplex.mappingCone.inr f)
    (CochainComplex.mappingCone.triangle f).mor₃
    (CochainComplex.mappingCone.inr_triangleδ f)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Every cone relation comes from a degreewise split short exact sequence. -/
lemma closedSupportConeShortComplex_shortExact (f : P ⟶ Q) :
    (closedSupportConeShortComplex P Q f).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro i
  let e := P.shiftFunctorObjXIso 1 i (i + 1) (by omega)
  let c := CochainComplex.mappingCone.inl f
  let t := c.v (i + 1) i (by omega)
  let split : ((closedSupportConeShortComplex P Q f).map
      (HomologicalComplex.eval _ _ i)).Splitting := {
    r := (CochainComplex.mappingCone.snd f).v i i (add_zero i)
    s := -(e.hom ≫ t)
    f_r := by simp [closedSupportConeShortComplex]
    s_g := by
      dsimp [closedSupportConeShortComplex, t, c]
      simp [e]
    id := by
      dsimp [closedSupportConeShortComplex]
      apply CochainComplex.mappingCone.ext_from f (i + 1) i rfl
      · simp [t, c, e]
      · simp [t, c, e] }
  exact split.shortExact

namespace K0WithSupport

/-- The concrete cone relation in closed-support K₀. -/
lemma mk_cone (f : P ⟶ Q) :
    mk Z (supportedPerfectOnObj Z (CochainComplex.mappingCone f)
      (strictlyPerfectComplex_mappingCone R f hp hq) (hsP.mappingCone f hsQ)) =
    mk Z (supportedPerfectOnObj Z Q hq hsQ) - mk Z (supportedPerfectOnObj Z P hp hsP) := by
  have h := mk_triangle Z _
    (supportedPerfectOnConeTriangle_distinguished Z P Q hp hq hsP hsQ f)
  exact eq_sub_of_add_eq' h.symm

/-- A quasi-isomorphism between supported perfect complexes preserves the K₀ class. -/
lemma mk_eq_of_quasiIso (f : P ⟶ Q) [QuasiIso f] :
    mk Z (supportedPerfectOnObj Z P hp hsP) = mk Z (supportedPerfectOnObj Z Q hq hsQ) := by
  obtain ⟨e, he⟩ := (strictlyPerfectComplex_quasiIso_iff hp hq f).mp inferInstance
  exact TriangulatedK0.mk_iso (ObjectProperty.isoMk _ (ObjectProperty.isoMk _
    (HomotopyCategory.isoOfHomotopyEquiv e)))

variable {P Q hp hq hsP hsQ}

/-- An acyclic supported perfect complex represents zero, with no Noetherian hypothesis. -/
lemma mk_eq_zero_of_acyclic (hp : strictlyPerfectComplex R P)
    (hsP : HasHomologySupportOn Z P) (hac : P.Acyclic) :
    mk Z (supportedPerfectOnObj Z P hp hsP) = 0 := by
  have := strictlyPerfectComplex_isKProjective hp
  let ht := CochainComplex.IsKProjective.homotopyZero (𝟙 P) hac
  have hz : IsZero ((homotopyQuot R).obj P) := by
    rw [IsZero.iff_id_eq_zero]
    have he : (homotopyQuot R).map (𝟙 P) = (homotopyQuot R).map 0 :=
      HomotopyCategory.eq_of_homotopy _ _ ht
    exact ((homotopyQuot R).map_id P).symm.trans (he.trans ((homotopyQuot R).map_zero P P))
  have hobj : IsZero (supportedPerfectOnObj Z P hp hsP) :=
    IsZero.of_full_of_faithful_of_isZero
      (supportedPerfectOnInclusion Z ⋙ perfectHomotopyInclusion R) _ hz
  exact TriangulatedK0.mk_of_isZero _ hobj

/-- Short exact sequences give the same additive relation as their mapping cones. -/
lemma mk_shortExact (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ))
    (hS : S.ShortExact)
    (h₁ : strictlyPerfectComplex R S.X₁) (h₂ : strictlyPerfectComplex R S.X₂)
    (h₃ : strictlyPerfectComplex R S.X₃)
    (s₁ : HasHomologySupportOn Z S.X₁) (s₂ : HasHomologySupportOn Z S.X₂)
    (s₃ : HasHomologySupportOn Z S.X₃) :
    mk Z (supportedPerfectOnObj Z S.X₂ h₂ s₂) =
      mk Z (supportedPerfectOnObj Z S.X₁ h₁ s₁) +
      mk Z (supportedPerfectOnObj Z S.X₃ h₃ s₃) := by
  have := CochainComplex.mappingCone.quasiIso_descShortComplex hS
  have he := mk_eq_of_quasiIso Z (CochainComplex.mappingCone S.f) S.X₃
    (strictlyPerfectComplex_mappingCone R S.f h₁ h₂) h₃ (s₁.mappingCone S.f s₂) s₃
    (CochainComplex.mappingCone.descShortComplex S)
  rw [← he, mk_cone Z S.X₁ S.X₂ h₁ h₂ s₁ s₂ S.f]
  abel

/-- Degreewise short exact sequences of supported perfect complexes give the same relation. -/
lemma mk_degreewise_shortExact (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ))
    (hS : ∀ i, (S.map (HomologicalComplex.eval _ _ i)).ShortExact)
    (h₁ : strictlyPerfectComplex R S.X₁) (h₂ : strictlyPerfectComplex R S.X₂)
    (h₃ : strictlyPerfectComplex R S.X₃)
    (s₁ : HasHomologySupportOn Z S.X₁) (s₂ : HasHomologySupportOn Z S.X₂)
    (s₃ : HasHomologySupportOn Z S.X₃) :
    mk Z (supportedPerfectOnObj Z S.X₂ h₂ s₂) =
      mk Z (supportedPerfectOnObj Z S.X₁ h₁ s₁) +
      mk Z (supportedPerfectOnObj Z S.X₃ h₃ s₃) :=
  mk_shortExact Z S (HomologicalComplex.shortExact_of_degreewise_shortExact S hS)
    h₁ h₂ h₃ s₁ s₂ s₃

/-- There are no nonzero Grothendieck classes with empty support. -/
lemma eq_zero_of_empty_support (x : K0WithSupport
    (⊥ : TopologicalSpace.Closeds (PrimeSpectrum R))) : x = 0 := by
  have h : AddMonoidHom.id (K0WithSupport (⊥ : TopologicalSpace.Closeds (PrimeSpectrum R))) =
      0 := by
    apply hom_ext
    intro X
    let P := X.obj.obj.as
    have hp : strictlyPerfectComplex R P :=
      (perfectHomotopyProperty_quotient R P).mp X.obj.property
    have hs : HasHomologySupportOn ⊥ P :=
      (perfectHomotopyObj_supportedOn_iff ⊥ P hp).mp X.property
    have hac : P.Acyclic := fun i ↦
      (HomologicalComplex.exactAt_iff_isZero_homology _ _).mpr
        (hasHomologySupportOn_bot_iff.mp hs i)
    change mk ⊥ X = 0
    rw [mk_iso ⊥
      (ObjectProperty.isoMk _ (ObjectProperty.isoMk _ (Iso.refl _)) :
        X ≅ supportedPerfectOnObj ⊥ P hp hs)]
    exact mk_eq_zero_of_acyclic ⊥ hp hs hac
  exact DFunLike.congr_fun h x

end K0WithSupport

/-- A null-homotopy of the identity makes a supported object zero. -/
lemma supportedPerfectOnObj_isZero_of_homotopy
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (hp : strictlyPerfectComplex R P)
    (hs : HasHomologySupportOn Z P) (ht : Homotopy (𝟙 P) 0) :
    IsZero (supportedPerfectOnObj Z P hp hs) :=
  IsZero.of_full_of_faithful_of_isZero
    (supportedPerfectOnInclusion Z ⋙ perfectHomotopyInclusion R) _
    ((HomotopyCategory.isZero_quotient_obj_iff P).mpr ⟨ht⟩)

variable {B : Type*} [AddCommGroup B]

/-- Additive evaluations using the short-exact-sequence presentation. -/
def ClosedSupportShortExactAdditive (χ : SupportedPerfectHomotopyOn Z → B) : Prop :=
  ∀ (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ)) (_ : S.ShortExact)
    (h₁ : strictlyPerfectComplex R S.X₁) (h₂ : strictlyPerfectComplex R S.X₂)
    (h₃ : strictlyPerfectComplex R S.X₃)
    (s₁ : HasHomologySupportOn Z S.X₁) (s₂ : HasHomologySupportOn Z S.X₂)
    (s₃ : HasHomologySupportOn Z S.X₃),
    χ (supportedPerfectOnObj Z S.X₂ h₂ s₂) =
      χ (supportedPerfectOnObj Z S.X₁ h₁ s₁) + χ (supportedPerfectOnObj Z S.X₃ h₃ s₃)

namespace ClosedSupportShortExactAdditive

variable {Z} {χ : SupportedPerfectHomotopyOn Z → B} (hχ : ClosedSupportShortExactAdditive Z χ)
  (hi : ∀ {X Y : SupportedPerfectHomotopyOn Z}, (X ≅ Y) → χ X = χ Y)

include hχ hi

lemma zero : χ (0 : SupportedPerfectHomotopyOn Z) = 0 := by
  let O : CochainComplex (ModuleCat.{u} R) ℤ := 0
  have hp : strictlyPerfectComplex R O := strictlyPerfectComplex_zero
  have hs : HasHomologySupportOn Z O := hasHomologySupportOn_of_isZero (isZero_zero _)
  let S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ) :=
    ShortComplex.mk (𝟙 O) (𝟙 O) (by simp [O])
  have hS : S.ShortExact := {
    exact := ShortComplex.exact_of_isZero_X₂ S (isZero_zero _)
    mono_f := inferInstance
    epi_g := inferInstance }
  have h := hχ S hS hp hp hp hs hs hs
  change χ (supportedPerfectOnObj Z O hp hs) =
    χ (supportedPerfectOnObj Z O hp hs) + χ (supportedPerfectOnObj Z O hp hs) at h
  have hz : χ (supportedPerfectOnObj Z O hp hs) = 0 :=
    add_left_cancel (a := χ (supportedPerfectOnObj Z O hp hs)) (by
      simpa only [add_zero] using h.symm)
  have ho : IsZero (supportedPerfectOnObj Z O hp hs) :=
    IsZero.of_full_of_faithful_of_isZero
      (supportedPerfectOnInclusion Z ⋙ perfectHomotopyInclusion R) _
      ((homotopyQuot R).map_isZero (isZero_zero _))
  rw [← hi (ho.iso (isZero_zero _))]
  exact hz

lemma shift_one (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (hp : strictlyPerfectComplex R P) (hs : HasHomologySupportOn Z P) :
    χ (supportedPerfectOnObj Z (P⟦(1 : ℤ)⟧) (strictlyPerfectComplex_shift hp 1) (hs.shift 1)) =
      -χ (supportedPerfectOnObj Z P hp hs) := by
  let hc := strictlyPerfectComplex_mappingCone R (𝟙 P) hp hp
  let sc := hs.mappingCone (𝟙 P) hs
  have hz := supportedPerfectOnObj_isZero_of_homotopy Z _ hc sc
    (CochainComplex.mappingCone.homotopyToZeroOfId P)
  have he := (hi (hz.iso (isZero_zero _))).trans (hχ.zero hi)
  have h := hχ (closedSupportConeShortComplex P P (𝟙 P))
    (closedSupportConeShortComplex_shortExact P P (𝟙 P)) hp hc
    (strictlyPerfectComplex_shift hp 1) hs sc (hs.shift 1)
  change χ (supportedPerfectOnObj Z _ hc sc) = _ at h
  rw [he] at h
  exact eq_neg_of_add_eq_zero_right h.symm

lemma cone (P Q : CochainComplex (ModuleCat.{u} R) ℤ)
    (hp : strictlyPerfectComplex R P) (hq : strictlyPerfectComplex R Q)
    (hsP : HasHomologySupportOn Z P) (hsQ : HasHomologySupportOn Z Q) (f : P ⟶ Q) :
    χ (supportedPerfectOnObj Z (CochainComplex.mappingCone f)
      (strictlyPerfectComplex_mappingCone R f hp hq) (hsP.mappingCone f hsQ)) =
      χ (supportedPerfectOnObj Z Q hq hsQ) - χ (supportedPerfectOnObj Z P hp hsP) := by
  have h := hχ (closedSupportConeShortComplex P Q f)
    (closedSupportConeShortComplex_shortExact P Q f) hq
    (strictlyPerfectComplex_mappingCone R f hp hq) (strictlyPerfectComplex_shift hp 1)
    hsQ (hsP.mappingCone f hsQ) (hsP.shift 1)
  change χ (supportedPerfectOnObj Z (CochainComplex.mappingCone f)
    (strictlyPerfectComplex_mappingCone R f hp hq) (hsP.mappingCone f hsQ)) =
    χ (supportedPerfectOnObj Z Q hq hsQ) +
    χ (supportedPerfectOnObj Z (P⟦(1 : ℤ)⟧)
      (strictlyPerfectComplex_shift hp 1) (hsP.shift 1)) at h
  rw [hχ.shift_one hi P hp hsP] at h
  exact h.trans (sub_eq_add_neg _ _).symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
lemma triangle (T : Triangle (SupportedPerfectHomotopyOn Z)) (hT : T ∈ distTriang _) :
    χ T.obj₂ = χ T.obj₁ + χ T.obj₃ := by
  let I := supportedPerfectOnInclusion Z ⋙ perfectHomotopyInclusion R
  let P := T.obj₁.obj.obj.as
  let Q := T.obj₂.obj.obj.as
  have hp : strictlyPerfectComplex R P :=
    (perfectHomotopyProperty_quotient R P).mp T.obj₁.obj.property
  have hq : strictlyPerfectComplex R Q :=
    (perfectHomotopyProperty_quotient R Q).mp T.obj₂.obj.property
  have sp : HasHomologySupportOn Z P :=
    (perfectHomotopyObj_supportedOn_iff Z P hp).mp T.obj₁.property
  have sq : HasHomologySupportOn Z Q :=
    (perfectHomotopyObj_supportedOn_iff Z Q hq).mp T.obj₂.property
  obtain ⟨f, ⟨e⟩⟩ := homotopyTriangle_exists_coneRepresentative
    (I.mapTriangle.obj T) (I.map_distinguished T hT)
  let ep : T.obj₁ ≅ supportedPerfectOnObj Z P hp sp :=
    ObjectProperty.isoMk _ (ObjectProperty.isoMk _ (Iso.refl _))
  let eq : T.obj₂ ≅ supportedPerfectOnObj Z Q hq sq :=
    ObjectProperty.isoMk _ (ObjectProperty.isoMk _ (Iso.refl _))
  let ec : T.obj₃ ≅ supportedPerfectOnObj Z (CochainComplex.mappingCone f)
      (strictlyPerfectComplex_mappingCone R f hp hq) (sp.mappingCone f sq) :=
    ObjectProperty.isoMk _ (ObjectProperty.isoMk _ e)
  rw [hi ep, hi eq, hi ec, hχ.cone hi P Q hp hq sp sq f]
  abel

end ClosedSupportShortExactAdditive

/-- The short-exact and distinguished-triangle presentations have the same additive evaluations.
Together with `strictlyPerfectComplex_quasiIso_iff`, this identifies their K₀ relations. -/
lemma closedSupport_shortExactAdditive_iff_triangleAdditive
    (χ : SupportedPerfectHomotopyOn Z → B)
    (hi : ∀ {X Y : SupportedPerfectHomotopyOn Z}, (X ≅ Y) → χ X = χ Y) :
    ClosedSupportShortExactAdditive Z χ ↔
      ∀ (T : Triangle (SupportedPerfectHomotopyOn Z)) (_ : T ∈ distTriang _),
        χ T.obj₂ = χ T.obj₁ + χ T.obj₃ := by
  constructor
  · exact fun h ↦ h.triangle hi
  · intro ht S hS h₁ h₂ h₃ s₁ s₂ s₃
    have h := ht (supportedPerfectOnConeTriangle Z S.X₁ S.X₂ h₁ h₂ s₁ s₂ S.f)
      (supportedPerfectOnConeTriangle_distinguished Z S.X₁ S.X₂ h₁ h₂ s₁ s₂ S.f)
    change χ (supportedPerfectOnObj Z S.X₂ h₂ s₂) =
      χ (supportedPerfectOnObj Z S.X₁ h₁ s₁) +
      χ (supportedPerfectOnObj Z (CochainComplex.mappingCone S.f)
        (strictlyPerfectComplex_mappingCone R S.f h₁ h₂) (s₁.mappingCone S.f s₂)) at h
    rw [hi (supportedPerfectOnConeIsoOfShortExact Z S hS h₁ h₂ h₃ s₁ s₂ s₃)] at h
    exact h

end SerrePositivity
