module

public import SerrePositivity.PerfectComplex.ClosedSupport
public import SerrePositivity.PerfectComplex.Perfect.HomotopyCategory
public import SerrePositivity.CategoryTheory.TriangulatedK0

/-! # 閉集合に台を持つ有限射影複体の K₀

## 概要

台の条件を閉集合へ拡張した有限射影複体の K₀ `K0WithSupport Z` を作り、等しい閉台の取り替えを与える。

## 方針

既存の有限射影ホモトピー圏の台の条件を閉集合版にする。

## 規約

有限自由の列版 `K0Supported` は変えない。

## 使われ方

`ClosedSupport/Functoriality`・`ClosedSupport/Cup`、KTheory。
-/

@[expose] public noncomputable section

universe u

section ClosedSupportK0Part

namespace SerrePositivity

open CategoryTheory Limits Pretriangulated
open scoped ZeroObject

variable {R : Type u} [CommRing R]

/-- Homology support on a closed set, as a property of the existing perfect homotopy category. -/
def perfectHomotopySupportedOn (Z : TopologicalSpace.Closeds (PrimeSpectrum R)) :
    ObjectProperty (PerfectHomotopy R) := fun X ↦ ∀ i : ℤ,
  Module.support R ((HomotopyCategory.homologyFunctor (ModuleCat.{u} R) (.up ℤ) i).obj
    X.obj) ⊆ Z

/-- The homotopy category condition agrees with support of the representative complex. -/
lemma perfectHomotopyObj_supportedOn_iff
    (Z : TopologicalSpace.Closeds (PrimeSpectrum R))
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (hP : strictlyPerfectComplex R P) :
    perfectHomotopySupportedOn Z (perfectHomotopyObj R P hP) ↔ HasHomologySupportOn Z P := by
  apply forall_congr'
  intro i
  exact (congrArg (fun s : Set (PrimeSpectrum R) ↦ s ⊆ (Z : Set (PrimeSpectrum R)))
    (((HomotopyCategory.homologyFunctorFactors _ _ i).app P).toLinearEquiv.support_eq)).to_iff

variable (Z : TopologicalSpace.Closeds (PrimeSpectrum R))

instance : (perfectHomotopySupportedOn Z).IsClosedUnderIsomorphisms where
  of_iso {X Y} e hX i := by
    let h : (HomotopyCategory.homologyFunctor (ModuleCat.{u} R) (.up ℤ) i).obj X.obj ≅
        (HomotopyCategory.homologyFunctor (ModuleCat.{u} R) (.up ℤ) i).obj Y.obj :=
      (HomotopyCategory.homologyFunctor (ModuleCat.{u} R) (.up ℤ) i).mapIso
      ((perfectHomotopyInclusion R).mapIso e)
    rw [← h.toLinearEquiv.support_eq]
    exact hX i

instance : (perfectHomotopySupportedOn Z).ContainsZero where
  exists_zero := ⟨0, isZero_zero _, fun i ↦ by
    have hz := ((perfectHomotopyInclusion R) ⋙
      HomotopyCategory.homologyFunctor (ModuleCat.{u} R) (.up ℤ) i).map_isZero
        (isZero_zero (PerfectHomotopy R))
    have : Subsingleton ((HomotopyCategory.homologyFunctor (ModuleCat.{u} R) (.up ℤ) i).obj
        (0 : PerfectHomotopy R).obj) := ModuleCat.subsingleton_of_isZero hz
    simp [Module.support_eq_empty]⟩

instance : (perfectHomotopySupportedOn Z).IsStableUnderShift ℤ where
  isStableUnderShiftBy n :=
    { le_shift X hX := by
        rw [ObjectProperty.prop_shift_iff]
        intro i
        let e : (HomotopyCategory.homologyFunctor (ModuleCat.{u} R) (.up ℤ) i).obj
            (X⟦n⟧).obj ≅
            (HomotopyCategory.homologyFunctor (ModuleCat.{u} R) (.up ℤ) (n + i)).obj X.obj :=
          (HomotopyCategory.homologyFunctor (ModuleCat.{u} R) (.up ℤ) i).mapIso
          (((perfectHomotopyInclusion R).commShiftIso n).app X) ≪≫
          ((HomotopyCategory.homologyFunctor (ModuleCat.{u} R) (.up ℤ) 0).shiftIso
            n i (n + i) rfl).app X.obj
        rw [e.toLinearEquiv.support_eq]
        exact hX (n + i) }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
instance : (perfectHomotopySupportedOn Z).IsTriangulatedClosed₃ where
  ext₃' T hT h₁ h₂ := by
    let P := T.obj₁.obj.as
    let Q := T.obj₂.obj.as
    have hp : strictlyPerfectComplex R P :=
      (perfectHomotopyProperty_quotient R P).mp T.obj₁.property
    have hq : strictlyPerfectComplex R Q :=
      (perfectHomotopyProperty_quotient R Q).mp T.obj₂.property
    have hsP : HasHomologySupportOn Z P :=
      (perfectHomotopyObj_supportedOn_iff Z P hp).mp h₁
    have hsQ : HasHomologySupportOn Z Q :=
      (perfectHomotopyObj_supportedOn_iff Z Q hq).mp h₂
    let I := perfectHomotopyInclusion R
    obtain ⟨f, ⟨e⟩⟩ := homotopyTriangle_exists_coneRepresentative
      (I.mapTriangle.obj T) (I.map_distinguished T hT)
    let hc := strictlyPerfectComplex_mappingCone R f hp hq
    let C := perfectHomotopyObj R (CochainComplex.mappingCone f) hc
    refine ⟨C, ?_, ⟨ObjectProperty.isoMk _ e⟩⟩
    exact (perfectHomotopyObj_supportedOn_iff Z _ hc).mpr (hsP.mappingCone f hsQ)

instance : (perfectHomotopySupportedOn Z).IsTriangulated where
  toIsTriangulatedClosed₂ := .of_isTriangulatedClosed₃

/-- The closed-support subcategory of the existing perfect homotopy category. -/
abbrev SupportedPerfectHomotopyOn := (perfectHomotopySupportedOn Z).FullSubcategory

/-- Forget the closed support, preserving distinguished triangles. -/
abbrev supportedPerfectOnInclusion : SupportedPerfectHomotopyOn Z ⥤ PerfectHomotopy R :=
  (perfectHomotopySupportedOn Z).ι

/-- Grothendieck group of perfect complexes with homology supported on `Z`. -/
abbrev K0WithSupport := TriangulatedK0 (SupportedPerfectHomotopyOn Z)

/-- A concrete supported perfect complex as an object of the support category. -/
def supportedPerfectOnObj (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (hP : strictlyPerfectComplex R P) (hs : HasHomologySupportOn Z P) :
    SupportedPerfectHomotopyOn Z :=
  ⟨perfectHomotopyObj R P hP, (perfectHomotopyObj_supportedOn_iff Z P hP).mpr hs⟩

namespace K0WithSupport

/-- The class of a supported perfect homotopy object. -/
abbrev mk (X : SupportedPerfectHomotopyOn Z) : K0WithSupport Z := TriangulatedK0.mk X

/-- Universal additive evaluation on the closed-support Grothendieck group. -/
noncomputable abbrev lift {B : Type*} [AddCommGroup B] (f : SupportedPerfectHomotopyOn Z → B)
    (hi : ∀ {X Y}, (X ≅ Y) → f X = f Y)
    (ht : ∀ T : Triangle (SupportedPerfectHomotopyOn Z), T ∈ distTriang _ →
      f T.obj₂ = f T.obj₁ + f T.obj₃) : K0WithSupport Z →+ B :=
  TriangulatedK0.lift f hi ht

lemma hom_ext {B : Type*} [AddCommGroup B] {f g : K0WithSupport Z →+ B}
    (h : ∀ X, f (mk Z X) = g (mk Z X)) : f = g := TriangulatedK0.hom_ext h

/-- Isomorphic supported objects have the same class. -/
lemma mk_iso {X Y : SupportedPerfectHomotopyOn Z} (e : X ≅ Y) :
    mk Z X = mk Z Y := TriangulatedK0.mk_iso e

/-- Distinguished triangles give the additive relation. -/
lemma mk_triangle (T : Triangle (SupportedPerfectHomotopyOn Z)) (hT : T ∈ distTriang _) :
    mk Z T.obj₂ = mk Z T.obj₁ + mk Z T.obj₃ := TriangulatedK0.mk_triangle T hT

@[simp] lemma mk_zero : mk Z (0 : SupportedPerfectHomotopyOn Z) = 0 :=
  TriangulatedK0.mk_zero

lemma mk_shift_one (X : SupportedPerfectHomotopyOn Z) :
    mk Z (X⟦(1 : ℤ)⟧) = -mk Z X := TriangulatedK0.mk_shift_one X

@[simp] lemma lift_mk {B : Type*} [AddCommGroup B] (f : SupportedPerfectHomotopyOn Z → B)
    (hi) (ht) (X : SupportedPerfectHomotopyOn Z) :
    lift Z f hi ht (mk Z X) = f X := TriangulatedK0.lift_mk ..

end K0WithSupport

end SerrePositivity

end ClosedSupportK0Part

section ClosedSupportCongrPart

namespace SerrePositivity
variable {R : Type u} [CommRing R]

/-- Change equal closed supports. -/
def supportedPerfectOnCongr {Z W : TopologicalSpace.Closeds (PrimeSpectrum R)}
    (h : Z = W) (X : SupportedPerfectHomotopyOn Z) : SupportedPerfectHomotopyOn W := by
  subst W
  exact X

lemma supportedPerfectOnCongr_obj {Z W : TopologicalSpace.Closeds (PrimeSpectrum R)}
    (h : Z = W) (X : SupportedPerfectHomotopyOn Z) :
    (supportedPerfectOnCongr h X).obj.obj = X.obj.obj := by
  subst W
  rfl

namespace K0WithSupport
/-- The additive equivalence obtained by changing equal supports. -/
def congr {Z W : TopologicalSpace.Closeds (PrimeSpectrum R)} (h : Z = W) :
    K0WithSupport Z ≃+ K0WithSupport W := by
  subst W
  exact AddEquiv.refl _

lemma congr_mk {Z W : TopologicalSpace.Closeds (PrimeSpectrum R)} (h : Z = W)
    (X : SupportedPerfectHomotopyOn Z) : congr h (mk _ X) = mk _ (supportedPerfectOnCongr h X) := by
  subst W
  rfl

end K0WithSupport
end SerrePositivity

end ClosedSupportCongrPart
