module
public import SerrePositivity.HomologicalAlgebra.BoundedAboveDerivedAcyclic
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT

/-! # Finite cohomology and Tor-acyclic derived scalar extension -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Pretriangulated
attribute [local instance] HasDerivedCategory.standard
variable {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)

lemma scalarExtensionTorVanishing_of_iso {M N : ModuleCat.{u} R} (e : M ≅ N)
    (hM : scalarExtensionTorVanishing φ M) : scalarExtensionTorVanishing φ N := by
  intro n hn
  exact (hM n hn).of_iso
    (((Tor (ModuleCat R) n).obj (baseChangeScalarModule φ)).mapIso e.symm)

/-- For a pure object, Tor-acyclicity of its actual homology preserves the lower bound. -/
lemma boundedAboveDerivedBaseChange_pure_isGE (X : DerivedCategory.Minus (ModuleCat.{u} R))
    (i : ℤ) [X.obj.IsGE i] [X.obj.IsLE i]
    (hX : scalarExtensionTorVanishing φ
      ((DerivedCategory.homologyFunctor (ModuleCat R) i).obj X.obj)) :
    ((boundedAboveDerivedBaseChange φ).obj X).obj.IsGE i := by
  obtain ⟨M, ⟨e⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE X.obj i
  let eH := (DerivedCategory.homologyFunctor (ModuleCat R) i).mapIso e ≪≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) i).app M
  have hM := scalarExtensionTorVanishing_of_iso φ eH hX
  let Y := (boundedAboveDerivedSingleFunctor.obj M)⟦-i⟧
  let eY : Y.obj ≅ (DerivedCategory.singleFunctor (ModuleCat R) i).obj M :=
    (DerivedCategory.Minus.ι.commShiftIso (-i)).app (boundedAboveDerivedSingleFunctor.obj M) ≪≫
      ((DerivedCategory.singleFunctors (ModuleCat R)).shiftIso (-i) i 0 (by omega)).app M
  let e' : X ≅ Y := ObjectProperty.isoMk _ (e ≪≫ eY.symm)
  have hY := boundedAboveDerivedBaseChangeAcyclicShift_isGE φ M hM (-i)
  have : ((boundedAboveDerivedBaseChange φ).obj Y).obj.IsGE i := by
    simpa only [neg_neg] using hY
  let ei : ((boundedAboveDerivedBaseChange φ).obj Y).obj ≅
      ((boundedAboveDerivedBaseChange φ).obj X).obj :=
    (DerivedCategory.Minus.ι.mapIso ((boundedAboveDerivedBaseChange φ).mapIso e')).symm
  exact DerivedCategory.TStructure.t.isGE_of_iso ei i

/-- The lower truncation inclusion preserves every homology degree at or below its cut. -/
lemma derivedTruncLE_homology_isIso (X : DerivedCategory (ModuleCat.{u} R))
    (n i : ℤ) (hi : i ≤ n) :
    IsIso ((DerivedCategory.homologyFunctor (ModuleCat R) i).map
      ((DerivedCategory.TStructure.t.truncLEι n).app X)) := by
  let t := DerivedCategory.TStructure.t (C := ModuleCat R)
  let T := (t.triangleLEGE n (n + 1) rfl).obj X
  have hT := t.triangleLEGE_distinguished n (n + 1) rfl X
  have : T.obj₃.IsGE (n + 1) := by dsimp [T]; infer_instance
  have h₀ := DerivedCategory.isZero_of_isGE T.obj₃ (n + 1) i (by omega)
  have h₁ := DerivedCategory.isZero_of_isGE T.obj₃ (n + 1) (i - 1) (by omega)
  have : Epi ((DerivedCategory.homologyFunctor (ModuleCat R) i).map T.mor₁) :=
    (DerivedCategory.HomologySequence.epi_homologyMap_mor₁_iff T hT i).mpr
      (h₀.eq_of_tgt _ _)
  have : Mono ((DerivedCategory.homologyFunctor (ModuleCat R) i).map T.mor₁) :=
    (DerivedCategory.HomologySequence.mono_homologyMap_mor₁_iff T hT (i - 1) i (by omega)).mpr
      (h₁.eq_of_src _ _)
  change IsIso ((DerivedCategory.homologyFunctor (ModuleCat R) i).map T.mor₁)
  exact isIso_of_mono_of_epi _

/-- The upper truncation projection preserves every homology degree at or above its cut. -/
lemma derivedTruncGE_homology_isIso (X : DerivedCategory (ModuleCat.{u} R))
    (n i : ℤ) (hi : n ≤ i) :
    IsIso ((DerivedCategory.homologyFunctor (ModuleCat R) i).map
      ((DerivedCategory.TStructure.t.truncGEπ n).app X)) := by
  let t := DerivedCategory.TStructure.t (C := ModuleCat R)
  let T := (t.triangleLEGE (n - 1) n (by omega)).obj X
  have hT := t.triangleLEGE_distinguished (n - 1) n (by omega) X
  have : T.obj₁.IsLE (n - 1) := by dsimp [T]; infer_instance
  have h₀ := DerivedCategory.isZero_of_isLE T.obj₁ (n - 1) i (by omega)
  have h₁ := DerivedCategory.isZero_of_isLE T.obj₁ (n - 1) (i + 1) (by omega)
  have : Mono ((DerivedCategory.homologyFunctor (ModuleCat R) i).map T.mor₂) :=
    (DerivedCategory.HomologySequence.mono_homologyMap_mor₂_iff T hT i).mpr
      (h₀.eq_of_src _ _)
  have : Epi ((DerivedCategory.homologyFunctor (ModuleCat R) i).map T.mor₂) :=
    (DerivedCategory.HomologySequence.epi_homologyMap_mor₂_iff T hT i (i + 1) rfl).mpr
      (h₁.eq_of_tgt _ _)
  change IsIso ((DerivedCategory.homologyFunctor (ModuleCat R) i).map T.mor₂)
  exact isIso_of_mono_of_epi _

/-- All cohomology modules are acyclic for the specified scalar extension. -/
def homologyTorAcyclic (X : DerivedCategory (ModuleCat.{u} R)) : Prop :=
  ∀ i : ℤ, scalarExtensionTorVanishing φ
    ((DerivedCategory.homologyFunctor (ModuleCat R) i).obj X)

lemma scalarExtensionTorVanishing_of_isZero (M : ModuleCat.{u} R) (hM : IsZero M) :
    scalarExtensionTorVanishing φ M := by
  intro n hn
  change IsZero
    (((((tensoringLeft (ModuleCat R)).obj (baseChangeScalarModule φ)).leftDerived n).obj M))
  exact (((tensoringLeft (ModuleCat R)).obj (baseChangeScalarModule φ)).leftDerived n).map_isZero hM

lemma homologyTorAcyclic_truncLE (X : DerivedCategory (ModuleCat.{u} R))
    (hX : homologyTorAcyclic φ X) (n : ℤ) :
    homologyTorAcyclic φ ((DerivedCategory.TStructure.t.truncLE n).obj X) := by
  intro i
  by_cases hi : i ≤ n
  · have := derivedTruncLE_homology_isIso X n i hi
    exact scalarExtensionTorVanishing_of_iso φ
      (asIso ((DerivedCategory.homologyFunctor (ModuleCat R) i).map
        ((DerivedCategory.TStructure.t.truncLEι n).app X))).symm (hX i)
  · exact scalarExtensionTorVanishing_of_isZero φ _
      (DerivedCategory.isZero_of_isLE _ n i (by omega))

lemma homologyTorAcyclic_truncGE (X : DerivedCategory (ModuleCat.{u} R))
    (hX : homologyTorAcyclic φ X) (n : ℤ) :
    homologyTorAcyclic φ ((DerivedCategory.TStructure.t.truncGE n).obj X) := by
  intro i
  by_cases hi : n ≤ i
  · have := derivedTruncGE_homology_isIso X n i hi
    exact scalarExtensionTorVanishing_of_iso φ
      (asIso ((DerivedCategory.homologyFunctor (ModuleCat R) i).map
        ((DerivedCategory.TStructure.t.truncGEπ n).app X))) (hX i)
  · exact scalarExtensionTorVanishing_of_isZero φ _
      (DerivedCategory.isZero_of_isGE _ n i (by omega))

/-- Finite Tor-acyclic cohomology prevents new cohomology below the original lower bound. -/
lemma boundedAboveDerivedBaseChange_finite_isGE (w : ℕ)
    (X : DerivedCategory.Minus (ModuleCat.{u} R)) (a : ℤ)
    [X.obj.IsGE a] [X.obj.IsLE (a + w)] (hX : homologyTorAcyclic φ X.obj) :
    ((boundedAboveDerivedBaseChange φ).obj X).obj.IsGE a := by
  induction w generalizing X a with
  | zero =>
    have : X.obj.IsLE a := by simpa using (inferInstance : X.obj.IsLE (a + (0 : ℕ)))
    exact boundedAboveDerivedBaseChange_pure_isGE φ X a (hX a)
  | succ w ih =>
    let t := DerivedCategory.TStructure.t (C := ModuleCat R)
    let n : ℤ := a + w
    have : X.obj.IsLE (n + 1) := by
      convert (inferInstance : X.obj.IsLE (a + (w + 1 : ℕ))) using 1
      dsimp [n]
      omega
    let A : DerivedCategory.Minus (ModuleCat R) :=
      ⟨(t.truncLE n).obj X.obj, ⟨n, inferInstance⟩⟩
    let B : DerivedCategory.Minus (ModuleCat R) :=
      ⟨(t.truncGE (n + 1)).obj X.obj, ⟨n + 1, inferInstance⟩⟩
    have : A.obj.IsGE a := by dsimp [A]; infer_instance
    have : A.obj.IsLE (a + w) := by dsimp [A, n]; infer_instance
    have hA := ih A a (homologyTorAcyclic_truncLE φ X.obj hX n)
    have : B.obj.IsGE (n + 1) := by dsimp [B]; infer_instance
    have : B.obj.IsLE (n + 1) := by dsimp [B]; infer_instance
    have hB := boundedAboveDerivedBaseChange_pure_isGE φ B (n + 1)
      ((homologyTorAcyclic_truncGE φ X.obj hX (n + 1)) (n + 1))
    let f : A ⟶ X := ObjectProperty.homMk ((t.truncLEι n).app X.obj)
    let g : X ⟶ B := ObjectProperty.homMk ((t.truncGEπ (n + 1)).app X.obj)
    let δ : B ⟶ A⟦(1 : ℤ)⟧ := ObjectProperty.homMk
      ((t.truncGEδLE n (n + 1) rfl).app X.obj ≫
        (DerivedCategory.Minus.ι.commShiftIso (1 : ℤ)).inv.app A)
    have hT : Triangle.mk f.hom g.hom
        (δ.hom ≫ (DerivedCategory.Minus.ι.commShiftIso (1 : ℤ)).hom.app A) ∈
          distTriang (DerivedCategory (ModuleCat R)) := by
      have ht := t.triangleLEGE_distinguished n (n + 1) rfl X.obj
      change Triangle.mk _ _ _ ∈ distTriang _ at ht
      dsimp only [f, g, δ, ObjectProperty.homMk_hom]
      simp only [Category.assoc, Iso.inv_hom_id_app]
      erw [Category.comp_id]
      exact ht
    have hTB := boundedAboveLeftDerivedTriangle_distinguished (ModuleCat.extendScalars φ) f g δ hT
    have hB' : ((boundedAboveDerivedBaseChange φ).obj B).obj.IsGE a :=
      DerivedCategory.TStructure.t.isGE_of_ge _ a (n + 1) (by dsimp [n]; omega)
    exact DerivedCategory.TStructure.t.isGE₂
      (boundedAboveLeftDerivedTriangle (ModuleCat.extendScalars φ) f g δ) hTB a hA hB'

/-- For a bounded-above object, finite Tor-acyclic cohomology preserves any lower bound. -/
lemma boundedAboveDerivedBaseChange_isGE_of_homologyTorAcyclic
    (X : DerivedCategory.Minus (ModuleCat.{u} R)) (a : ℤ) [X.obj.IsGE a]
    (hX : homologyTorAcyclic φ X.obj) :
    ((boundedAboveDerivedBaseChange φ).obj X).obj.IsGE a := by
  obtain ⟨b, hb⟩ := X.property
  have : X.obj.IsLE (a + (b - a).toNat) :=
    DerivedCategory.TStructure.t.isLE_of_le X.obj b (a + (b - a).toNat) (by omega)
  exact boundedAboveDerivedBaseChange_finite_isGE φ (b - a).toNat X a hX

end SerrePositivity
