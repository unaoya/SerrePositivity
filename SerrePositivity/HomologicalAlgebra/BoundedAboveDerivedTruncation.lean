module
public import SerrePositivity.HomologicalAlgebra.FiniteCohomologyBaseChange

/-! # Standard truncations in the bounded-above derived category and their derived images -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe v u
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits Pretriangulated
attribute [local instance] HasDerivedCategory.standard
variable (C : Type u) [Category.{v} C] [Abelian C]

/-- The standard lower truncation restricted to bounded-above derived objects. -/
def boundedAboveDerivedTruncLE (n : ℤ) : DerivedCategory.Minus C ⥤ DerivedCategory.Minus C :=
  DerivedCategory.TStructure.t.minus.lift
    (DerivedCategory.Minus.ι ⋙ DerivedCategory.TStructure.t.truncLE n) (by
      intro X
      change ∃ b : ℤ, ((DerivedCategory.TStructure.t.truncLE n).obj X.obj).IsLE b
      exact ⟨n, inferInstance⟩)

/-- The standard upper truncation restricted to bounded-above derived objects. -/
def boundedAboveDerivedTruncGE (n : ℤ) : DerivedCategory.Minus C ⥤ DerivedCategory.Minus C :=
  DerivedCategory.TStructure.t.minus.lift
    (DerivedCategory.Minus.ι ⋙ DerivedCategory.TStructure.t.truncGE n) (by
      intro X
      obtain ⟨b, hb⟩ := X.property
      change ∃ b : ℤ, ((DerivedCategory.TStructure.t.truncGE n).obj X.obj).IsLE b
      exact ⟨b, inferInstance⟩)

/-- The natural lower truncation inclusion inside the bounded-above category. -/
def boundedAboveDerivedTruncLEι (n : ℤ) : boundedAboveDerivedTruncLE C n ⟶ 𝟭 _ where
  app X := ObjectProperty.homMk ((DerivedCategory.TStructure.t.truncLEι n).app X.obj)
  naturality {X Y} f := by
    apply InducedCategory.hom_ext
    exact (DerivedCategory.TStructure.t.truncLEι n).naturality f.hom

/-- The natural upper truncation projection inside the bounded-above category. -/
def boundedAboveDerivedTruncGEπ (n : ℤ) : 𝟭 _ ⟶ boundedAboveDerivedTruncGE C n where
  app X := ObjectProperty.homMk ((DerivedCategory.TStructure.t.truncGEπ n).app X.obj)
  naturality {X Y} f := by
    apply InducedCategory.hom_ext
    exact (DerivedCategory.TStructure.t.truncGEπ n).naturality f.hom

/-- The connecting map uses the actual shift of the bounded-above category. -/
def boundedAboveDerivedTruncδ (n : ℤ) (X : DerivedCategory.Minus C) :
    (boundedAboveDerivedTruncGE C (n + 1)).obj X ⟶
      ((boundedAboveDerivedTruncLE C n).obj X)⟦(1 : ℤ)⟧ :=
  ObjectProperty.homMk ((DerivedCategory.TStructure.t.truncGEδLE n (n + 1) rfl).app X.obj ≫
    (DerivedCategory.Minus.ι.commShiftIso (1 : ℤ)).inv.app
      ((boundedAboveDerivedTruncLE C n).obj X))

lemma boundedAboveDerivedTrunc_distinguished (n : ℤ) (X : DerivedCategory.Minus C) :
    Triangle.mk ((boundedAboveDerivedTruncLEι C n).app X).hom
      ((boundedAboveDerivedTruncGEπ C (n + 1)).app X).hom
      ((boundedAboveDerivedTruncδ C n X).hom ≫
        (DerivedCategory.Minus.ι.commShiftIso (1 : ℤ)).hom.app
          ((boundedAboveDerivedTruncLE C n).obj X)) ∈ distTriang (DerivedCategory C) := by
  have ht := DerivedCategory.TStructure.t.triangleLEGE_distinguished n (n + 1) rfl X.obj
  change Triangle.mk _ _ _ ∈ distTriang _ at ht
  dsimp only [boundedAboveDerivedTruncLEι, boundedAboveDerivedTruncGEπ,
    boundedAboveDerivedTruncδ, ObjectProperty.homMk_hom]
  simp only [Category.assoc, Iso.inv_hom_id_app]
  erw [Category.comp_id]
  exact ht

variable {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)

/-- For Tor-acyclic cohomology, deriving a lower truncation preserves its retained homology. -/
lemma boundedAboveDerivedBaseChange_truncLE_homology_isIso
    (X : DerivedCategory.Minus (ModuleCat.{u} R)) (hX : homologyTorAcyclic φ X.obj)
    (n i : ℤ) (hi : i ≤ n) :
    IsIso ((DerivedCategory.homologyFunctor (ModuleCat S) i).map
      ((boundedAboveDerivedBaseChange φ).map
        ((boundedAboveDerivedTruncLEι (ModuleCat R) n).app X)).hom) := by
  let A := (boundedAboveDerivedTruncLE (ModuleCat R) n).obj X
  let B := (boundedAboveDerivedTruncGE (ModuleCat R) (n + 1)).obj X
  let f := (boundedAboveDerivedTruncLEι (ModuleCat R) n).app X
  let g := (boundedAboveDerivedTruncGEπ (ModuleCat R) (n + 1)).app X
  let δ := boundedAboveDerivedTruncδ (ModuleCat R) n X
  have : B.obj.IsGE (n + 1) := by
    change ((DerivedCategory.TStructure.t.truncGE _).obj _).IsGE _
    infer_instance
  have hB := boundedAboveDerivedBaseChange_isGE_of_homologyTorAcyclic φ B (n + 1)
    (homologyTorAcyclic_truncGE φ X.obj hX (n + 1))
  let T := boundedAboveLeftDerivedTriangle (ModuleCat.extendScalars φ) f g δ
  have hT := boundedAboveLeftDerivedTriangle_distinguished (ModuleCat.extendScalars φ) f g δ
    (boundedAboveDerivedTrunc_distinguished (ModuleCat R) n X)
  have : T.obj₃.IsGE (n + 1) := hB
  have h₀ := DerivedCategory.isZero_of_isGE T.obj₃ (n + 1) i (by omega)
  have h₁ := DerivedCategory.isZero_of_isGE T.obj₃ (n + 1) (i - 1) (by omega)
  have : Epi ((DerivedCategory.homologyFunctor (ModuleCat S) i).map T.mor₁) :=
    (DerivedCategory.HomologySequence.epi_homologyMap_mor₁_iff T hT i).mpr (h₀.eq_of_tgt _ _)
  have : Mono ((DerivedCategory.homologyFunctor (ModuleCat S) i).map T.mor₁) :=
    (DerivedCategory.HomologySequence.mono_homologyMap_mor₁_iff T hT (i - 1) i (by omega)).mpr
      (h₁.eq_of_src _ _)
  change IsIso ((DerivedCategory.homologyFunctor (ModuleCat S) i).map T.mor₁)
  exact isIso_of_mono_of_epi _

/-- Upper truncation preserves its retained derived-image homology without a Tor hypothesis. -/
lemma boundedAboveDerivedBaseChange_truncGE_homology_isIso
    (X : DerivedCategory.Minus (ModuleCat.{u} R)) (n i : ℤ) (hi : n ≤ i) :
    IsIso ((DerivedCategory.homologyFunctor (ModuleCat S) i).map
      ((boundedAboveDerivedBaseChange φ).map
        ((boundedAboveDerivedTruncGEπ (ModuleCat R) n).app X)).hom) := by
  let A := (boundedAboveDerivedTruncLE (ModuleCat R) (n - 1)).obj X
  let f := (boundedAboveDerivedTruncLEι (ModuleCat R) (n - 1)).app X
  let B := (boundedAboveDerivedTruncGE (ModuleCat R) ((n - 1) + 1)).obj X
  let g := (boundedAboveDerivedTruncGEπ (ModuleCat R) ((n - 1) + 1)).app X
  let δ := boundedAboveDerivedTruncδ (ModuleCat R) (n - 1) X
  have : A.obj.IsLE (n - 1) := by
    change ((DerivedCategory.TStructure.t.truncLE _).obj _).IsLE _
    infer_instance
  have hA := boundedAboveLeftDerived_isLE (ModuleCat.extendScalars φ) A (n - 1)
  let T := boundedAboveLeftDerivedTriangle (ModuleCat.extendScalars φ) f g δ
  have hT := boundedAboveLeftDerivedTriangle_distinguished (ModuleCat.extendScalars φ) f g δ
    (boundedAboveDerivedTrunc_distinguished (ModuleCat R) (n - 1) X)
  have : T.obj₁.IsLE (n - 1) := hA
  have h₀ := DerivedCategory.isZero_of_isLE T.obj₁ (n - 1) i (by omega)
  have h₁ := DerivedCategory.isZero_of_isLE T.obj₁ (n - 1) (i + 1) (by omega)
  have : Mono ((DerivedCategory.homologyFunctor (ModuleCat S) i).map T.mor₂) :=
    (DerivedCategory.HomologySequence.mono_homologyMap_mor₂_iff T hT i).mpr (h₀.eq_of_src _ _)
  have : Epi ((DerivedCategory.homologyFunctor (ModuleCat S) i).map T.mor₂) :=
    (DerivedCategory.HomologySequence.epi_homologyMap_mor₂_iff T hT i (i + 1) rfl).mpr
      (h₁.eq_of_tgt _ _)
  have hiso : IsIso ((DerivedCategory.homologyFunctor (ModuleCat S) i).map T.mor₂) :=
    isIso_of_mono_of_epi _
  change IsIso ((DerivedCategory.homologyFunctor (ModuleCat S) i).map
    ((boundedAboveDerivedBaseChange φ).map
      ((boundedAboveDerivedTruncGEπ (ModuleCat R) ((n - 1) + 1)).app X)).hom) at hiso
  exact (congrArg (fun k : ℤ => IsIso
    ((DerivedCategory.homologyFunctor (ModuleCat S) i).map
      ((boundedAboveDerivedBaseChange φ).map
        ((boundedAboveDerivedTruncGEπ (ModuleCat R) k).app X)).hom))
      (show n - 1 + 1 = n by omega)).mp hiso

end SerrePositivity
