module
public import SerrePositivity.HomologicalAlgebra.BoundedAboveDerivedTruncation
public import SerrePositivity.HomologicalAlgebra.DerivedAcyclicSingle

/-! # Natural homology base change for bounded-above objects with Tor-acyclic cohomology -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R]

/-- Actual homology on the standard bounded-above derived category. -/
abbrev boundedAboveDerivedHomology (i : ℤ) :
    DerivedCategory.Minus (ModuleCat.{u} R) ⥤ ModuleCat.{u} R :=
  DerivedCategory.Minus.ι ⋙ DerivedCategory.homologyFunctor (ModuleCat R) i

/-- The lower truncation inclusion is naturally an isomorphism on the retained homology. -/
def boundedAboveTruncLEHomologyNatIso (i : ℤ) :
    boundedAboveDerivedTruncLE (ModuleCat R) i ⋙ boundedAboveDerivedHomology R i ≅
      boundedAboveDerivedHomology R i := by
  let α : boundedAboveDerivedTruncLE (ModuleCat R) i ⋙ boundedAboveDerivedHomology R i ⟶
      boundedAboveDerivedHomology R i :=
    Functor.whiskerRight (boundedAboveDerivedTruncLEι (ModuleCat R) i)
      (boundedAboveDerivedHomology R i)
  refine NatIso.ofComponents (fun X => by
    have : IsIso (α.app X) := derivedTruncLE_homology_isIso X.obj i i le_rfl
    exact asIso (α.app X)) ?_
  intro X Y f
  exact α.naturality f

/-- The upper truncation projection is naturally an isomorphism on the retained homology. -/
def boundedAboveTruncGEHomologyNatIso (i : ℤ) :
    boundedAboveDerivedHomology R i ≅
      boundedAboveDerivedTruncGE (ModuleCat R) i ⋙ boundedAboveDerivedHomology R i := by
  let α : boundedAboveDerivedHomology R i ⟶
      boundedAboveDerivedTruncGE (ModuleCat R) i ⋙ boundedAboveDerivedHomology R i :=
    Functor.whiskerRight (boundedAboveDerivedTruncGEπ (ModuleCat R) i)
      (boundedAboveDerivedHomology R i)
  refine NatIso.ofComponents (fun X => by
    have : IsIso (α.app X) := derivedTruncGE_homology_isIso X.obj i i le_rfl
    exact asIso (α.app X)) ?_
  intro X Y f
  exact α.naturality f

/-- The pure layer in degree i, built from the two standard truncations. -/
abbrev boundedAboveDerivedLayer (i : ℤ) :
    DerivedCategory.Minus (ModuleCat.{u} R) ⥤ DerivedCategory.Minus (ModuleCat.{u} R) :=
  boundedAboveDerivedTruncLE (ModuleCat R) i ⋙ boundedAboveDerivedTruncGE (ModuleCat R) i

instance boundedAboveDerivedLayer_isLE (i : ℤ) (X : DerivedCategory.Minus (ModuleCat.{u} R)) :
    ((boundedAboveDerivedLayer R i).obj X).obj.IsLE i := by
  change ((DerivedCategory.TStructure.t.truncGE i).obj
    ((DerivedCategory.TStructure.t.truncLE i).obj X.obj)).IsLE i
  infer_instance

instance boundedAboveDerivedLayer_isGE (i : ℤ) (X : DerivedCategory.Minus (ModuleCat.{u} R)) :
    ((boundedAboveDerivedLayer R i).obj X).obj.IsGE i := by
  change ((DerivedCategory.TStructure.t.truncGE i).obj
    ((DerivedCategory.TStructure.t.truncLE i).obj X.obj)).IsGE i
  infer_instance

/-- The pure layer has canonically the original object's homology in its degree. -/
def boundedAboveDerivedLayerHomologyNatIso (i : ℤ) :
    boundedAboveDerivedLayer R i ⋙ boundedAboveDerivedHomology R i ≅
      boundedAboveDerivedHomology R i :=
  Functor.isoWhiskerLeft (boundedAboveDerivedTruncLE (ModuleCat R) i)
      (boundedAboveTruncGEHomologyNatIso R i).symm ≪≫ boundedAboveTruncLEHomologyNatIso R i

variable {R} {S : Type u} [CommRing S] (φ : R →+* S)

/-- The full subcategory with Tor-acyclic actual cohomology; no lower bound is imposed. -/
def homologyTorAcyclicProperty : ObjectProperty (DerivedCategory.Minus (ModuleCat.{u} R)) :=
  fun X => homologyTorAcyclic φ X.obj

/-- The lower truncation remains an isomorphism on derived-image homology on this subcategory. -/
def acyclicDerivedTruncLEHomologyNatIso (i : ℤ) :
    (homologyTorAcyclicProperty φ).ι ⋙ boundedAboveDerivedTruncLE (ModuleCat R) i ⋙
        boundedAboveDerivedBaseChange φ ⋙ boundedAboveDerivedHomology S i ≅
      (homologyTorAcyclicProperty φ).ι ⋙ boundedAboveDerivedBaseChange φ ⋙
        boundedAboveDerivedHomology S i := by
  let G := boundedAboveDerivedBaseChange φ ⋙ boundedAboveDerivedHomology S i
  let α := Functor.whiskerLeft (homologyTorAcyclicProperty φ).ι
    (Functor.whiskerRight (boundedAboveDerivedTruncLEι (ModuleCat R) i) G)
  refine NatIso.ofComponents (fun X => by
    have : IsIso (α.app X) :=
      boundedAboveDerivedBaseChange_truncLE_homology_isIso φ X.obj X.property i i le_rfl
    exact asIso (α.app X)) ?_
  intro X Y f
  exact α.naturality f

/-- The upper truncation always remains an isomorphism on retained derived-image homology. -/
def derivedTruncGEHomologyNatIso (i : ℤ) :
    boundedAboveDerivedBaseChange φ ⋙ boundedAboveDerivedHomology S i ≅
      boundedAboveDerivedTruncGE (ModuleCat R) i ⋙ boundedAboveDerivedBaseChange φ ⋙
        boundedAboveDerivedHomology S i := by
  let G := boundedAboveDerivedBaseChange φ ⋙ boundedAboveDerivedHomology S i
  let α := Functor.whiskerRight (boundedAboveDerivedTruncGEπ (ModuleCat R) i) G
  refine NatIso.ofComponents (fun X => by
    have : IsIso (α.app X) :=
      boundedAboveDerivedBaseChange_truncGE_homology_isIso φ X i i le_rfl
    exact asIso (α.app X)) ?_
  intro X Y f
  exact α.naturality f

/-- The pure-layer calculation is natural on all objects with Tor-acyclic cohomology. -/
def acyclicDerivedLayerHomologyNatIso (i : ℤ) :
    (homologyTorAcyclicProperty φ).ι ⋙ boundedAboveDerivedLayer R i ⋙
        boundedAboveDerivedBaseChange φ ⋙ boundedAboveDerivedHomology S i ≅
      (homologyTorAcyclicProperty φ).ι ⋙ boundedAboveDerivedLayer R i ⋙
        boundedAboveDerivedHomology R i ⋙ ModuleCat.extendScalars φ := by
  refine NatIso.ofComponents (fun X => boundedAboveDerivedBaseChangePureHomologyIso φ
    ((boundedAboveDerivedLayer R i).obj X.obj) i
    ((homologyTorAcyclic_truncGE φ _
      (homologyTorAcyclic_truncLE φ X.obj.obj X.property i) i) i)) ?_
  intro X Y f
  exact boundedAboveDerivedBaseChangePureHomologyIso_naturality φ i
    ((boundedAboveDerivedLayer R i).map f.hom) _ _

/-- Actual derived scalar extension commutes naturally with homology of Tor-acyclic objects. -/
def acyclicDerivedHomologyNatIso (i : ℤ) :
    (homologyTorAcyclicProperty φ).ι ⋙ boundedAboveDerivedBaseChange φ ⋙
        boundedAboveDerivedHomology S i ≅
      (homologyTorAcyclicProperty φ).ι ⋙ boundedAboveDerivedHomology R i ⋙
        ModuleCat.extendScalars φ :=
  (acyclicDerivedTruncLEHomologyNatIso φ i).symm ≪≫
    Functor.isoWhiskerLeft
      ((homologyTorAcyclicProperty φ).ι ⋙ boundedAboveDerivedTruncLE (ModuleCat R) i)
      (derivedTruncGEHomologyNatIso φ i) ≪≫
    acyclicDerivedLayerHomologyNatIso φ i ≪≫
    Functor.isoWhiskerLeft (homologyTorAcyclicProperty φ).ι
      (Functor.isoWhiskerRight (boundedAboveDerivedLayerHomologyNatIso R i)
        (ModuleCat.extendScalars φ))

/-- Pointwise form of the natural actual homology comparison, with explicit Tor hypotheses. -/
def boundedAboveDerivedBaseChangeHomologyIso
    (X : DerivedCategory.Minus (ModuleCat.{u} R)) (hX : homologyTorAcyclic φ X.obj) (i : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat S) i).obj
        ((boundedAboveDerivedBaseChange φ).obj X).obj ≅
      (ModuleCat.extendScalars φ).obj
        ((DerivedCategory.homologyFunctor (ModuleCat R) i).obj X.obj) :=
  (acyclicDerivedHomologyNatIso φ i).app ⟨X, hX⟩

lemma boundedAboveDerivedBaseChangeHomologyIso_naturality
    {X Y : DerivedCategory.Minus (ModuleCat.{u} R)}
    (hX : homologyTorAcyclic φ X.obj) (hY : homologyTorAcyclic φ Y.obj) (f : X ⟶ Y) (i : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat S) i).map
        ((boundedAboveDerivedBaseChange φ).map f).hom ≫
        (boundedAboveDerivedBaseChangeHomologyIso φ Y hY i).hom =
      (boundedAboveDerivedBaseChangeHomologyIso φ X hX i).hom ≫
        (ModuleCat.extendScalars φ).map
          ((DerivedCategory.homologyFunctor (ModuleCat R) i).map f.hom) :=
  (acyclicDerivedHomologyNatIso φ i).hom.naturality
    (show (⟨X, hX⟩ : (homologyTorAcyclicProperty φ).FullSubcategory) ⟶ ⟨Y, hY⟩ from
      ObjectProperty.homMk f)

/-- Zero homology maps after derivation are detected by ordinary scalar extension. -/
lemma boundedAboveDerivedHomology_map_eq_zero_iff
    {X Y : DerivedCategory.Minus (ModuleCat.{u} R)}
    (hX : homologyTorAcyclic φ X.obj) (hY : homologyTorAcyclic φ Y.obj) (f : X ⟶ Y) (i : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat S) i).map
        ((boundedAboveDerivedBaseChange φ).map f).hom = 0 ↔
      (ModuleCat.extendScalars φ).map
        ((DerivedCategory.homologyFunctor (ModuleCat R) i).map f.hom) = 0 := by
  have hn := boundedAboveDerivedBaseChangeHomologyIso_naturality φ hX hY f i
  constructor
  · intro h
    apply (cancel_epi (boundedAboveDerivedBaseChangeHomologyIso φ X hX i).hom).mp
    rw [← hn, h, zero_comp, comp_zero]
  · intro h
    apply (cancel_mono (boundedAboveDerivedBaseChangeHomologyIso φ Y hY i).hom).mp
    rw [hn, h, comp_zero, zero_comp]

end SerrePositivity
