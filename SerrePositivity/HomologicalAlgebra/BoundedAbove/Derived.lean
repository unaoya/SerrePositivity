module

public import SerrePositivity.HomologicalAlgebra.KProjectiveLift
public import Mathlib.Algebra.Homology.Factorizations.CM5a
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.Algebra.Homology.HomotopyCategory.Shift
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated

/-! # 上に有界な複体の射影分解と左導来関手

## 概要

上に有界な cochain 複体の射影分解 `BoundedAboveProjectiveResolution` と導来圏の対象の射影代表 `BoundedAboveDerivedModel` を作り、その関手性をホモトピー圏で示す。これにより、上に有界な導来圏上の左導来関手 `boundedAboveLeftDerived` を定め、加法性・線形性、シフト、写像錐、錐の三角形が完全三角形になることを示す。元の加法関手の完全性は仮定しない。

## 方針

代表の存在は K 射影的な持ち上げ（Mathlib の `IsKProjective`）から取り、関手性はホモトピーの一意性による。錐の代表は射影的な代表の錐である。

## 規約

`ofBoundedAbove`・`ofIsLE`・`comparison`・`map` は存在定理の `.choose` で作っている。Mathlib の `equivOfIsKProjective` から直接作る候補（refactor-plan §3.2.5）。BS が使う名前は残す。

## 使われ方

HomologicalAlgebra/BoundedAbove/Tensor、BoundedAboveDerivedAssociator・BaseChange（BS が使う）、導来完備化。
-/

@[expose] public noncomputable section

universe v u v' u' t

section BoundedAboveProjectiveResolutionPart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Opposite HomologicalComplex
namespace SerrePositivity
variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Reverse degrees and take opposites back to the original abelian category. -/
def cochainUnop (K : CochainComplex Cᵒᵖ ℤ) : CochainComplex C ℤ :=
  ((CochainComplex.opEquivalence C).inverse.obj K).unop

def cochainUnopMap {K L : CochainComplex Cᵒᵖ ℤ} (f : K ⟶ L) :
    cochainUnop L ⟶ cochainUnop K :=
  ((CochainComplex.opEquivalence C).inverse.map f).unop

lemma cochainUnopMap_quasiIso {K L : CochainComplex Cᵒᵖ ℤ}
    (f : K ⟶ L) [QuasiIso f] : QuasiIso (cochainUnopMap f) := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff' _ (n - 1) n (n + 1) (by simp) (by simp)]
  have hf : QuasiIsoAt f (-n) := inferInstance
  rw [quasiIsoAt_iff' _ (-(n + 1)) (-n) (-(n - 1)) (by simp; omega)
    (by simp; omega)] at hf
  have := hf
  exact ShortComplex.quasiIso_unopMap ((shortComplexFunctor' Cᵒᵖ (.up ℤ)
    (-(n + 1)) (-n) (-(n - 1))).map f)

/-- Every bounded-above complex has a bounded-above projective resolution,
with the same upper bound. -/
lemma exists_boundedAbove_projective_resolution [EnoughProjectives C]
    (K : CochainComplex C ℤ) (n : ℤ) [K.IsStrictlyLE n] :
    ∃ (P : CochainComplex C ℤ) (ε : P ⟶ K) (_ : QuasiIso ε)
      (_ : ∀ i, Projective (P.X i)), P.IsStrictlyLE n := by
  let K' := (CochainComplex.opEquivalence C).functor.obj (op K)
  have : K'.IsStrictlyGE (-n) := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro i hi
    exact (K.isZero_of_isStrictlyLE n (-i) (by omega)).op
  obtain ⟨L, i, hi, hL, hb⟩ :=
    CochainComplex.Plus.modelCategoryQuillen.exists_quasiIso_injective K' (-n)
  let e : cochainUnop K' ≅ K :=
    ((CochainComplex.opEquivalence C).unitIso.app (op K)).unop
  have : QuasiIso (cochainUnopMap i) := cochainUnopMap_quasiIso i
  refine ⟨cochainUnop L, cochainUnopMap i ≫ e.hom, inferInstance, ?_, ?_⟩
  · intro q
    exact inferInstanceAs (Projective (unop (L.X (-q))))
  · rw [CochainComplex.isStrictlyLE_iff]
    intro q hq
    exact (L.isZero_of_isStrictlyGE (-n) (-q) (by omega)).unop

/-- A projective replacement that may extend arbitrarily far into negative degrees. -/
structure BoundedAboveProjectiveResolution (K : CochainComplex C ℤ) where
  complex : CochainComplex C ℤ
  bound : ℤ
  bounded : complex.IsStrictlyLE bound
  projective : ∀ i, Projective (complex.X i)
  π : complex ⟶ K
  quasiIso : QuasiIso π

namespace BoundedAboveProjectiveResolution
attribute [instance] bounded projective quasiIso
variable {K : CochainComplex C ℤ}

instance isKProjective (P : BoundedAboveProjectiveResolution K) : P.complex.IsKProjective :=
  CochainComplex.isKProjective_of_projective P.complex P.bound

/-- Choose a projective replacement without a finite projective dimension assumption. -/
def ofBoundedAbove [EnoughProjectives C] (K : CochainComplex C ℤ)
    (n : ℤ) [K.IsStrictlyLE n] : BoundedAboveProjectiveResolution K :=
  Classical.choice (by
    obtain ⟨P, ε, hε, hP, hb⟩ := exists_boundedAbove_projective_resolution K n
    exact ⟨⟨P, n, hb, hP, ε, hε⟩⟩)

/-- Comparison of any two replacements, compatible with their augmentations up to homotopy. -/
def comparison (P Q : BoundedAboveProjectiveResolution K) : P.complex ⟶ Q.complex :=
  (exists_lift_of_quasiIso Q.π P.π).choose

def comparisonHomotopy (P Q : BoundedAboveProjectiveResolution K) :
    Homotopy (comparison P Q ≫ Q.π) P.π :=
  (exists_lift_of_quasiIso Q.π P.π).choose_spec.some

lemma comparison_quasiIso (P Q : BoundedAboveProjectiveResolution K) :
    QuasiIso (comparison P Q) := by
  have : QuasiIso (comparison P Q ≫ Q.π) := by
    rw [quasiIso_iff]
    intro i
    rw [quasiIsoAt_iff_isIso_homologyMap,
      (comparisonHomotopy P Q).homologyMap_eq i]
    infer_instance
  exact quasiIso_of_comp_right (comparison P Q) Q.π

/-- Different replacements are homotopy equivalent, with the chosen comparison as hom. -/
def comparisonHomotopyEquiv (P Q : BoundedAboveProjectiveResolution K) :
    HomotopyEquiv P.complex Q.complex :=
  ((CochainComplex.IsKProjective.quasiIso_iff (comparison P Q)).mp
    (comparison_quasiIso P Q)).choose

lemma comparisonHomotopyEquiv_hom (P Q : BoundedAboveProjectiveResolution K) :
    (comparisonHomotopyEquiv P Q).hom = comparison P Q :=
  ((CochainComplex.IsKProjective.quasiIso_iff (comparison P Q)).mp
    (comparison_quasiIso P Q)).choose_spec

end BoundedAboveProjectiveResolution

end SerrePositivity

end BoundedAboveProjectiveResolutionPart

section BoundedAboveResolutionFunctorPart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace SerrePositivity
variable {C : Type u} [Category.{v} C] [Abelian C]
attribute [local instance] HasDerivedCategory.standard

/-- Maps out of a K-projective complex that agree in the derived category are homotopic. -/
def homotopyOfDerivedMapEq {P X : CochainComplex C ℤ} [P.IsKProjective]
    (f g : P ⟶ X) (h : DerivedCategory.Q.map f = DerivedCategory.Q.map g) : Homotopy f g := by
  apply HomotopyCategory.homotopyOfEq
  apply (CochainComplex.IsKProjective.Qh_map_bijective P _).injective
  apply (cancel_mono ((DerivedCategory.quotientCompQhIso C).hom.app X)).mp
  rw [DerivedCategory.quotientCompQhIso_hom_naturality,
    DerivedCategory.quotientCompQhIso_hom_naturality, h]

namespace BoundedAboveProjectiveResolution
variable {K L M : CochainComplex C ℤ}

/-- Lift a map between the original complexes to their replacements. -/
def map (P : BoundedAboveProjectiveResolution K) (Q : BoundedAboveProjectiveResolution L)
    (f : K ⟶ L) : P.complex ⟶ Q.complex :=
  (exists_lift_of_quasiIso Q.π (P.π ≫ f)).choose

def mapHomotopy (P : BoundedAboveProjectiveResolution K)
    (Q : BoundedAboveProjectiveResolution L) (f : K ⟶ L) :
    Homotopy (map P Q f ≫ Q.π) (P.π ≫ f) :=
  (exists_lift_of_quasiIso Q.π (P.π ≫ f)).choose_spec.some

lemma map_naturality (P : BoundedAboveProjectiveResolution K)
    (Q : BoundedAboveProjectiveResolution L) (f : K ⟶ L) :
    DerivedCategory.Q.map (map P Q f) ≫ DerivedCategory.Q.map Q.π =
      DerivedCategory.Q.map P.π ≫ DerivedCategory.Q.map f := by
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
  exact DerivedCategory.Q_map_eq_of_homotopy C (mapHomotopy P Q f)

/-- Lifts are unique up to homotopy; this also controls all choices in composition. -/
def homotopyOfAugmentation (P : BoundedAboveProjectiveResolution K)
    (Q : BoundedAboveProjectiveResolution L) (f g : P.complex ⟶ Q.complex)
    (h : DerivedCategory.Q.map f ≫ DerivedCategory.Q.map Q.π =
      DerivedCategory.Q.map g ≫ DerivedCategory.Q.map Q.π) : Homotopy f g :=
  homotopyOfDerivedMapEq f g ((cancel_mono (DerivedCategory.Q.map Q.π)).mp h)

def mapIdHomotopy (P : BoundedAboveProjectiveResolution K) :
    Homotopy (map P P (𝟙 K)) (𝟙 P.complex) := by
  apply homotopyOfAugmentation P P
  rw [map_naturality]
  simp

def mapCompHomotopy (P : BoundedAboveProjectiveResolution K)
    (Q : BoundedAboveProjectiveResolution L) (T : BoundedAboveProjectiveResolution M)
    (f : K ⟶ L) (g : L ⟶ M) :
    Homotopy (map P T (f ≫ g)) (map P Q f ≫ map Q T g) := by
  apply homotopyOfAugmentation P T
  rw [map_naturality, CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
  simp only [Category.assoc]
  rw [map_naturality Q T g,
    ← Category.assoc (DerivedCategory.Q.map (map P Q f)), map_naturality P Q f,
    Category.assoc]

lemma map_quasiIso (P : BoundedAboveProjectiveResolution K)
    (Q : BoundedAboveProjectiveResolution L) (f : K ⟶ L) [QuasiIso f] :
    QuasiIso (map P Q f) := by
  rw [← DerivedCategory.isIso_Q_map_iff_quasiIso]
  have : IsIso (DerivedCategory.Q.map (map P Q f) ≫ DerivedCategory.Q.map Q.π) := by
    rw [map_naturality]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (DerivedCategory.Q.map Q.π)
end BoundedAboveProjectiveResolution

/-- Strictly bounded-above cochain complexes, with arbitrary chain maps. -/
abbrev BoundedAboveCochain (C : Type u) [Category.{v} C] [Abelian C] :=
  (show ObjectProperty (CochainComplex C ℤ) from fun K => ∃ n : ℤ, K.IsStrictlyLE n).FullSubcategory

/-- Choose a replacement for every object of the bounded-above category. -/
def boundedAboveChosenResolution [EnoughProjectives C] (K : BoundedAboveCochain C) :
    BoundedAboveProjectiveResolution K.obj := by
  have := K.property.choose_spec
  exact BoundedAboveProjectiveResolution.ofBoundedAbove K.obj K.property.choose

end SerrePositivity

end BoundedAboveResolutionFunctorPart

section BoundedAboveDerivedModelsPart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace SerrePositivity
attribute [local instance] HasDerivedCategory.standard
variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Every derived morphism out of a K-projective complex has a chain representative. -/
lemma exists_cochainMap_of_isKProjective {P X : CochainComplex C ℤ} [P.IsKProjective]
    (f : DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj X) :
    ∃ g : P ⟶ X, DerivedCategory.Q.map g = f := by
  obtain ⟨g, hg⟩ := (CochainComplex.IsKProjective.Qh_map_bijective P _).surjective
    ((DerivedCategory.quotientCompQhIso C).hom.app P ≫ f ≫
      (DerivedCategory.quotientCompQhIso C).inv.app X)
  obtain ⟨g, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective g
  refine ⟨g, ?_⟩
  apply (cancel_epi ((DerivedCategory.quotientCompQhIso C).hom.app P)).mp
  rw [← DerivedCategory.quotientCompQhIso_hom_naturality, hg]
  simp

/-- A bounded-above projective representative with an isomorphism to the actual derived object. -/
structure BoundedAboveDerivedModel (X : DerivedCategory C) where
  complex : CochainComplex C ℤ
  bound : ℤ
  bounded : complex.IsStrictlyLE bound
  projective : ∀ i, Projective (complex.X i)
  iso : DerivedCategory.Q.obj complex ≅ X

namespace BoundedAboveDerivedModel
attribute [instance] bounded projective
variable {X Y Z : DerivedCategory C}
instance isKProjective (P : BoundedAboveDerivedModel X) : P.complex.IsKProjective :=
  CochainComplex.isKProjective_of_projective P.complex P.bound

/-- A representative exists for every bounded-above derived object. -/
def ofIsLE [EnoughProjectives C] (X : DerivedCategory C) (n : ℤ) [X.IsLE n] :
    BoundedAboveDerivedModel X := Classical.choice (by
  obtain ⟨K, hb, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isLE X n
  let P := BoundedAboveProjectiveResolution.ofBoundedAbove K n
  exact ⟨⟨P.complex, P.bound, inferInstance, inferInstance,
    asIso (DerivedCategory.Q.map P.π) ≪≫ e.symm⟩⟩)

/-- A chain representative of a derived morphism, using the specified model isomorphisms. -/
def map (P : BoundedAboveDerivedModel X) (Q : BoundedAboveDerivedModel Y) (f : X ⟶ Y) :
    P.complex ⟶ Q.complex :=
  (exists_cochainMap_of_isKProjective (P.iso.hom ≫ f ≫ Q.iso.inv)).choose

lemma map_Q (P : BoundedAboveDerivedModel X) (Q : BoundedAboveDerivedModel Y) (f : X ⟶ Y) :
    DerivedCategory.Q.map (map P Q f) = P.iso.hom ≫ f ≫ Q.iso.inv :=
  (exists_cochainMap_of_isKProjective (P.iso.hom ≫ f ≫ Q.iso.inv)).choose_spec

lemma map_naturality (P : BoundedAboveDerivedModel X) (Q : BoundedAboveDerivedModel Y)
    (f : X ⟶ Y) :
    DerivedCategory.Q.map (map P Q f) ≫ Q.iso.hom = P.iso.hom ≫ f := by
  rw [map_Q]
  simp

def mapIdHomotopy (P : BoundedAboveDerivedModel X) :
    Homotopy (map P P (𝟙 X)) (𝟙 P.complex) :=
  homotopyOfDerivedMapEq _ _ (by rw [map_Q]; simp)

def mapCompHomotopy (P : BoundedAboveDerivedModel X) (Q : BoundedAboveDerivedModel Y)
    (T : BoundedAboveDerivedModel Z) (f : X ⟶ Y) (g : Y ⟶ Z) :
    Homotopy (map P T (f ≫ g)) (map P Q f ≫ map Q T g) :=
  homotopyOfDerivedMapEq _ _ (by rw [Functor.map_comp, map_Q, map_Q, map_Q]; simp)

lemma map_quasiIso (P : BoundedAboveDerivedModel X) (Q : BoundedAboveDerivedModel Y)
    (f : X ⟶ Y) [IsIso f] : QuasiIso (map P Q f) := by
  rw [← DerivedCategory.isIso_Q_map_iff_quasiIso, map_Q]
  infer_instance

/-- Comparing models is compatible with every derived morphism, up to homotopy. -/
def mapSquareHomotopy (P P' : BoundedAboveDerivedModel X)
    (Q Q' : BoundedAboveDerivedModel Y) (f : X ⟶ Y) :
    Homotopy (map P Q f ≫ map Q Q' (𝟙 Y)) (map P P' (𝟙 X) ≫ map P' Q' f) :=
  homotopyOfDerivedMapEq _ _ (by rw [Functor.map_comp, Functor.map_comp,
    map_Q, map_Q, map_Q, map_Q]; simp)

/-- An augmented resolution is a model of the actual derived image of its original complex. -/
def ofResolution {K : CochainComplex C ℤ} (P : BoundedAboveProjectiveResolution K) :
    BoundedAboveDerivedModel (DerivedCategory.Q.obj K) where
  complex := P.complex
  bound := P.bound
  bounded := inferInstance
  projective := inferInstance
  iso := asIso (DerivedCategory.Q.map P.π)

/-- The model lift of a localized chain map agrees with the augmented resolution lift. -/
def ofResolutionMapHomotopy {K L : CochainComplex C ℤ}
    (P : BoundedAboveProjectiveResolution K) (Q : BoundedAboveProjectiveResolution L)
    (f : K ⟶ L) :
    Homotopy (map (ofResolution P) (ofResolution Q) (DerivedCategory.Q.map f)) (P.map Q f) := by
  apply homotopyOfDerivedMapEq
  apply (cancel_mono (DerivedCategory.Q.map Q.π)).mp
  exact (map_naturality (ofResolution P) (ofResolution Q) (DerivedCategory.Q.map f)).trans
    (P.map_naturality Q f).symm

/-- Any chain map inducing the specified derived morphism agrees with its chosen lift. -/
def mapHomotopyOfNaturality (P : BoundedAboveDerivedModel X) (Q : BoundedAboveDerivedModel Y)
    (f : X ⟶ Y) (h : P.complex ⟶ Q.complex)
    (hh : DerivedCategory.Q.map h ≫ Q.iso.hom = P.iso.hom ≫ f) :
    Homotopy (map P Q f) h := by
  apply homotopyOfDerivedMapEq
  apply (cancel_mono Q.iso.hom).mp
  exact (map_naturality P Q f).trans hh.symm

end BoundedAboveDerivedModel

/-- Choose a projective model for each object of Mathlib's actual bounded-above derived category. -/
def boundedAboveDerivedChosenModel [EnoughProjectives C] (X : DerivedCategory.Minus C) :
    BoundedAboveDerivedModel X.obj := by
  have := X.property.choose_spec
  exact BoundedAboveDerivedModel.ofIsLE X.obj X.property.choose

/-- Restrict the standard derived localization to the bounded-above objects. -/
def boundedAboveDerivedQ : BoundedAboveCochain C ⥤ DerivedCategory.Minus C where
  obj K := by
    have := K.property.choose_spec
    exact ⟨DerivedCategory.Q.obj K.obj, ⟨K.property.choose, inferInstance⟩⟩
  map f := ObjectProperty.homMk (DerivedCategory.Q.map f.hom)
  map_id K := by
    apply InducedCategory.hom_ext
    change DerivedCategory.Q.map (𝟙 K.obj) = 𝟙 (DerivedCategory.Q.obj K.obj)
    exact CategoryTheory.Functor.map_id _ _
  map_comp f g := by
    apply InducedCategory.hom_ext
    change DerivedCategory.Q.map (f.hom ≫ g.hom) = _
    exact CategoryTheory.Functor.map_comp _ _ _

end SerrePositivity

end BoundedAboveDerivedModelsPart

section BoundedAboveLeftDerivedPart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
namespace SerrePositivity
attribute [local instance] HasDerivedCategory.standard
variable {C : Type u} [Category.{v} C] [Abelian C]
variable {E : Type u'} [Category.{v'} E] [Abelian E]
variable (F : C ⥤ E) [F.Additive]

/-- An additive functor preserves quasi-isomorphisms between K-projective complexes. -/
lemma mapCochain_quasiIso_of_KProjective {P Q : CochainComplex C ℤ}
    [P.IsKProjective] [Q.IsKProjective] (f : P ⟶ Q) [QuasiIso f] :
    QuasiIso ((F.mapHomologicalComplex (.up ℤ)).map f) := by
  obtain ⟨e, he⟩ := (CochainComplex.IsKProjective.quasiIso_iff f).mp inferInstance
  have h : (F.mapHomotopyEquiv e).hom = (F.mapHomologicalComplex (.up ℤ)).map f := by
    simp [Functor.mapHomotopyEquiv, he]
  rw [← h]
  infer_instance

/-- Compute the left derived functor using bounded-above projective representatives.
The source and target are Mathlib's standard derived categories. -/
def boundedAboveLeftDerived [EnoughProjectives C] :
    DerivedCategory.Minus C ⥤ DerivedCategory.Minus E where
  obj X := by
    let P := boundedAboveDerivedChosenModel X
    exact ⟨DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj P.complex),
      ⟨P.bound, inferInstance⟩⟩
  map {X Y} f := ObjectProperty.homMk (DerivedCategory.Q.map
    ((F.mapHomologicalComplex (.up ℤ)).map
      ((boundedAboveDerivedChosenModel X).map (boundedAboveDerivedChosenModel Y) f.hom)))
  map_id X := by
    apply InducedCategory.hom_ext
    let P := boundedAboveDerivedChosenModel X
    change DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map (P.map P (𝟙 X.obj))) = _
    rw [DerivedCategory.Q_map_eq_of_homotopy E (F.mapHomotopy P.mapIdHomotopy),
      CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
    rfl
  map_comp {X Y Z} f g := by
    apply InducedCategory.hom_ext
    let P := boundedAboveDerivedChosenModel X
    let Q := boundedAboveDerivedChosenModel Y
    let T := boundedAboveDerivedChosenModel Z
    change DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map
      (P.map T (f.hom ≫ g.hom))) =
      DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map (P.map Q f.hom)) ≫
        DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map (Q.map T g.hom))
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
    exact DerivedCategory.Q_map_eq_of_homotopy E
      (F.mapHomotopy (P.mapCompHomotopy Q T f.hom g.hom))

/-- Any bounded-above projective model computes the derived functor. -/
def boundedAboveLeftDerivedModelIso [EnoughProjectives C]
    (X : DerivedCategory.Minus C) (P : BoundedAboveDerivedModel X.obj) :
    ((boundedAboveLeftDerived F).obj X).obj ≅
      DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj P.complex) := by
  let A := boundedAboveDerivedChosenModel X
  have := A.map_quasiIso P (𝟙 X.obj)
  have := mapCochain_quasiIso_of_KProjective F (A.map P (𝟙 X.obj))
  exact asIso (DerivedCategory.Q.map
    ((F.mapHomologicalComplex (.up ℤ)).map (A.map P (𝟙 X.obj))))

/-- The computation with arbitrary models is natural in any representative of a derived morphism. -/
lemma boundedAboveLeftDerivedModelIso_naturality [EnoughProjectives C]
    {X Y : DerivedCategory.Minus C} (P : BoundedAboveDerivedModel X.obj)
    (Q : BoundedAboveDerivedModel Y.obj) (f : X ⟶ Y) (h : P.complex ⟶ Q.complex)
    (hh : DerivedCategory.Q.map h ≫ Q.iso.hom = P.iso.hom ≫ f.hom) :
    ((boundedAboveLeftDerived F).map f).hom ≫ (boundedAboveLeftDerivedModelIso F Y Q).hom =
      (boundedAboveLeftDerivedModelIso F X P).hom ≫
        DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map h) := by
  let A := boundedAboveDerivedChosenModel X
  let B := boundedAboveDerivedChosenModel Y
  have ht := (A.mapSquareHomotopy P B Q f.hom).trans
    ((P.mapHomotopyOfNaturality Q f.hom h hh).compLeft (A.map P (𝟙 _)))
  change DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map (A.map B f.hom)) ≫
      DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map (B.map Q (𝟙 _))) =
    DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map (A.map P (𝟙 _))) ≫
      DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map h)
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
    ← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
  exact DerivedCategory.Q_map_eq_of_homotopy E (F.mapHomotopy ht)

end SerrePositivity

end BoundedAboveLeftDerivedPart

section BoundedAboveDerivedAdditivePart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {C : Type u} [Category.{v} C] [Abelian C] [EnoughProjectives C]
variable {E : Type u'} [Category.{v'} E] [Abelian E]

/-- Chosen projective lifts respect addition up to homotopy. -/
def BoundedAboveDerivedModel.mapAddHomotopy {X Y : DerivedCategory C}
    (P : BoundedAboveDerivedModel X) (Q : BoundedAboveDerivedModel Y) (f g : X ⟶ Y) :
    Homotopy (P.map Q (f + g)) (P.map Q f + P.map Q g) :=
  P.mapHomotopyOfNaturality Q (f + g) _ (by
    simp only [Functor.map_add, Preadditive.add_comp, Preadditive.comp_add,
      P.map_naturality Q f, P.map_naturality Q g])

instance boundedAboveLeftDerived_additive (F : C ⥤ E) [F.Additive] :
    (boundedAboveLeftDerived F).Additive where
  map_add {X Y f g} := by
    apply InducedCategory.hom_ext
    let P := boundedAboveDerivedChosenModel X
    let Q := boundedAboveDerivedChosenModel Y
    change DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map
      (P.map Q (f.hom + g.hom))) = _
    rw [DerivedCategory.Q_map_eq_of_homotopy E (F.mapHomotopy
      (P.mapAddHomotopy Q f.hom g.hom)), Functor.map_add, Functor.map_add]
    rfl

variable (A : Type t) [CommRing A] [Linear A C] [Linear A E]

/-- Chosen projective lifts respect scalar multiplication up to homotopy. -/
def BoundedAboveDerivedModel.mapSmulHomotopy {X Y : DerivedCategory C}
    (P : BoundedAboveDerivedModel X) (Q : BoundedAboveDerivedModel Y) (a : A) (f : X ⟶ Y) :
    Homotopy (P.map Q (a • f)) (a • P.map Q f) :=
  P.mapHomotopyOfNaturality Q (a • f) _ (by
    simp only [Functor.map_smul, Linear.smul_comp, Linear.comp_smul, P.map_naturality Q f])

instance boundedAboveLeftDerived_linear (F : C ⥤ E) [F.Additive] [F.Linear A] :
    (boundedAboveLeftDerived F).Linear A where
  map_smul {X Y} f a := by
    apply InducedCategory.hom_ext
    let P := boundedAboveDerivedChosenModel X
    let Q := boundedAboveDerivedChosenModel Y
    change DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map
      (P.map Q (a • f.hom))) = _
    rw [DerivedCategory.Q_map_eq_of_homotopy E (F.mapHomotopy
      (P.mapSmulHomotopy A Q a f.hom)), Functor.map_smul, Functor.map_smul]
    rfl

end SerrePositivity

end BoundedAboveDerivedAdditivePart

section BoundedAboveDerivedShiftPart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits HomologicalComplex
attribute [local instance] HasDerivedCategory.standard
variable {C : Type u} [Category.{v} C] [Abelian C]
variable {E : Type u'} [Category.{v'} E] [Abelian E]

/-- Transport a projective representative along an actual derived isomorphism. -/
def BoundedAboveDerivedModel.transport {X Y : DerivedCategory C}
    (P : BoundedAboveDerivedModel X) (e : X ≅ Y) : BoundedAboveDerivedModel Y where
  complex := P.complex
  bound := P.bound
  bounded := P.bounded
  projective := P.projective
  iso := P.iso ≪≫ e

/-- Shift a bounded-above projective representative, retaining the actual derived shift. -/
def BoundedAboveDerivedModel.shift {X : DerivedCategory C} (P : BoundedAboveDerivedModel X)
    (n : ℤ) : BoundedAboveDerivedModel (X⟦n⟧) where
  complex := P.complex⟦n⟧
  bound := P.bound - n
  bounded := CochainComplex.isStrictlyLE_shift P.complex P.bound n (P.bound - n) (by omega)
  projective i := Projective.of_iso
    (CochainComplex.shiftFunctorObjXIso P.complex n i (i + n) rfl).symm inferInstance
  iso := (DerivedCategory.Q.commShiftIso n).app P.complex ≪≫
    (shiftFunctor (DerivedCategory C) n).mapIso P.iso

/-- A representative of a derived morphism shifts to a representative of its actual shift. -/
lemma BoundedAboveDerivedModel.shift_map_naturality {X Y : DerivedCategory C}
    (P : BoundedAboveDerivedModel X) (Q : BoundedAboveDerivedModel Y)
    (f : X ⟶ Y) (h : P.complex ⟶ Q.complex)
    (hh : DerivedCategory.Q.map h ≫ Q.iso.hom = P.iso.hom ≫ f) (n : ℤ) :
    DerivedCategory.Q.map (h⟦n⟧') ≫ (Q.shift n).iso.hom =
      (P.shift n).iso.hom ≫ f⟦n⟧' := by
  have hn := (DerivedCategory.Q.commShiftIso n).hom.naturality h
  change DerivedCategory.Q.map (h⟦n⟧') ≫ (DerivedCategory.Q.commShiftIso n).hom.app Q.complex =
    (DerivedCategory.Q.commShiftIso n).hom.app P.complex ≫ (DerivedCategory.Q.map h)⟦n⟧' at hn
  simp only [BoundedAboveDerivedModel.shift, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom]
  rw [← Category.assoc, hn, Category.assoc, ← CategoryTheory.Functor.map_comp, hh,
    CategoryTheory.Functor.map_comp]
  simp only [Category.assoc]

/-- Use the inclusion's shift isomorphism to model the actual full-subcategory shift. -/
def BoundedAboveDerivedModel.shiftMinus {X : DerivedCategory.Minus C}
    (P : BoundedAboveDerivedModel X.obj) (n : ℤ) : BoundedAboveDerivedModel (X⟦n⟧).obj :=
  (P.shift n).transport ((DerivedCategory.Minus.ι.commShiftIso n).app X).symm

/-- Shifted representatives respect the actual shift of a full-subcategory morphism. -/
lemma BoundedAboveDerivedModel.shiftMinus_map_naturality
    {X Y : DerivedCategory.Minus C} (P : BoundedAboveDerivedModel X.obj)
    (Q : BoundedAboveDerivedModel Y.obj) (f : X ⟶ Y) (h : P.complex ⟶ Q.complex)
    (hh : DerivedCategory.Q.map h ≫ Q.iso.hom = P.iso.hom ≫ f.hom) (n : ℤ) :
    DerivedCategory.Q.map (h⟦n⟧') ≫ (Q.shiftMinus n).iso.hom =
      (P.shiftMinus n).iso.hom ≫ (f⟦n⟧').hom := by
  simp only [BoundedAboveDerivedModel.shiftMinus, BoundedAboveDerivedModel.transport,
    Iso.trans_hom, Iso.symm_hom, Category.assoc]
  rw [← Category.assoc, P.shift_map_naturality Q f.hom h hh n, Category.assoc]
  congr 1
  exact (DerivedCategory.Minus.ι.commShiftIso n).inv.naturality f

/-- Compute the shift comparison of the left-derived functor using the chosen projective model. -/
def boundedAboveLeftDerivedShiftIso [EnoughProjectives C] (F : C ⥤ E) [F.Additive]
    (X : DerivedCategory.Minus C) (n : ℤ) :
    ((boundedAboveLeftDerived F).obj (X⟦n⟧)).obj ≅
      (((boundedAboveLeftDerived F).obj X).obj)⟦n⟧ := by
  let P := boundedAboveDerivedChosenModel X
  refine boundedAboveLeftDerivedModelIso F _ (P.shiftMinus n) ≪≫ ?_
  change DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj (P.complex⟦n⟧)) ≅ _
  exact DerivedCategory.Q.mapIso
      (((F.mapHomologicalComplex (.up ℤ)).commShiftIso n).app P.complex) ≪≫
    (DerivedCategory.Q.commShiftIso n).app ((F.mapHomologicalComplex (.up ℤ)).obj P.complex) ≪≫
    (shiftFunctor (DerivedCategory E) n).mapIso (boundedAboveLeftDerivedModelIso F X P).symm

/-- The left-derived shift comparison is natural in every actual derived morphism. -/
lemma boundedAboveLeftDerivedShiftIso_naturality [EnoughProjectives C] (F : C ⥤ E) [F.Additive]
    {X Y : DerivedCategory.Minus C} (f : X ⟶ Y) (n : ℤ) :
    ((boundedAboveLeftDerived F).map (f⟦n⟧')).hom ≫
        (boundedAboveLeftDerivedShiftIso F Y n).hom =
      (boundedAboveLeftDerivedShiftIso F X n).hom ≫
        (((boundedAboveLeftDerived F).map f).hom)⟦n⟧' := by
  let P := boundedAboveDerivedChosenModel X
  let Q := boundedAboveDerivedChosenModel Y
  let h := P.map Q f.hom
  let Fh := (F.mapHomologicalComplex (.up ℤ)).map h
  have hm := boundedAboveLeftDerivedModelIso_naturality F (P.shiftMinus n) (Q.shiftMinus n)
    (f⟦n⟧') (h⟦n⟧') (P.shiftMinus_map_naturality Q f h (P.map_naturality Q f.hom) n)
  have hc := ((F.mapHomologicalComplex (.up ℤ)).commShiftIso n).hom.naturality h
  change (F.mapHomologicalComplex (.up ℤ)).map (h⟦n⟧') ≫
      (((F.mapHomologicalComplex (.up ℤ)).commShiftIso n).app Q.complex).hom =
    (((F.mapHomologicalComplex (.up ℤ)).commShiftIso n).app P.complex).hom ≫ Fh⟦n⟧' at hc
  have hq := (DerivedCategory.Q.commShiftIso n).hom.naturality Fh
  change DerivedCategory.Q.map (Fh⟦n⟧') ≫
      ((DerivedCategory.Q.commShiftIso n).app
        ((F.mapHomologicalComplex (.up ℤ)).obj Q.complex)).hom =
    ((DerivedCategory.Q.commShiftIso n).app
      ((F.mapHomologicalComplex (.up ℤ)).obj P.complex)).hom ≫
      (DerivedCategory.Q.map Fh)⟦n⟧' at hq
  have hb := boundedAboveLeftDerivedModelIso_naturality F P Q f h (P.map_naturality Q f.hom)
  have hi : DerivedCategory.Q.map Fh ≫ (boundedAboveLeftDerivedModelIso F Y Q).inv =
      (boundedAboveLeftDerivedModelIso F X P).inv ≫ ((boundedAboveLeftDerived F).map f).hom := by
    apply (cancel_epi (boundedAboveLeftDerivedModelIso F X P).hom).mp
    rw [← Category.assoc, ← hb]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]
  simp only [boundedAboveLeftDerivedShiftIso, id_eq, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom, Category.assoc]
  rw [← Category.assoc, hm]
  simp only [Category.assoc]
  congr 1
  rw [← Category.assoc, ← CategoryTheory.Functor.map_comp, hc,
    CategoryTheory.Functor.map_comp]
  simp only [Category.assoc]
  congr 1
  rw [← Category.assoc, hq, Category.assoc]
  congr 1
  simpa only [CategoryTheory.Functor.map_comp] using
    congrArg (shiftFunctor (DerivedCategory E) n).map hi

end SerrePositivity

end BoundedAboveDerivedShiftPart

section BoundedAboveDerivedConePart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits HomologicalComplex
attribute [local instance] HasDerivedCategory.standard
variable {C : Type u} [Category.{v} C] [Abelian C]
variable {E : Type u'} [Category.{v'} E] [Abelian E]

/-- The cone of bounded-above projective representatives is itself such a representative. -/
def BoundedAboveDerivedModel.cone {X Y : DerivedCategory C}
    (P : BoundedAboveDerivedModel X) (Q : BoundedAboveDerivedModel Y) (f : P.complex ⟶ Q.complex) :
    BoundedAboveDerivedModel (DerivedCategory.Q.obj (CochainComplex.mappingCone f)) where
  complex := CochainComplex.mappingCone f
  bound := max P.bound Q.bound
  bounded := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    rw [CochainComplex.mappingCone.isZero_X_iff]
    exact ⟨P.complex.isZero_of_isStrictlyLE P.bound (i + 1) (by omega),
      Q.complex.isZero_of_isStrictlyLE Q.bound i (by omega)⟩
  projective i := Projective.of_iso
    (homotopyCofiber.XIsoBiprod f i (i + 1) rfl).symm inferInstance
  iso := Iso.refl _

/-- The actual bounded-above derived object of the model cone. -/
def boundedAboveDerivedConeObject {X Y : DerivedCategory C}
    (P : BoundedAboveDerivedModel X) (Q : BoundedAboveDerivedModel Y) (f : P.complex ⟶ Q.complex) :
    DerivedCategory.Minus C := by
  have : (CochainComplex.mappingCone f).IsStrictlyLE (max P.bound Q.bound) := (P.cone Q f).bounded
  exact ⟨DerivedCategory.Q.obj (CochainComplex.mappingCone f), ⟨max P.bound Q.bound, inferInstance⟩⟩

/-- The right cone inclusion, transported from any projective model of its actual source. -/
def boundedAboveDerivedConeInr {X : DerivedCategory C} {Y : DerivedCategory.Minus C}
    (P : BoundedAboveDerivedModel X) (Q : BoundedAboveDerivedModel Y.obj)
    (f : P.complex ⟶ Q.complex) : Y ⟶ boundedAboveDerivedConeObject P Q f :=
  ObjectProperty.homMk (Q.iso.inv ≫ DerivedCategory.Q.map (CochainComplex.mappingCone.inr f))

/-- The derived image of a projective cone is computed by the actual mapped cone. -/
def boundedAboveLeftDerivedConeIso [EnoughProjectives C] (F : C ⥤ E) [F.Additive]
    {X Y : DerivedCategory C} (P : BoundedAboveDerivedModel X) (Q : BoundedAboveDerivedModel Y)
    (f : P.complex ⟶ Q.complex) :
    ((boundedAboveLeftDerived F).obj (boundedAboveDerivedConeObject P Q f)).obj ≅
      DerivedCategory.Q.obj (CochainComplex.mappingCone
        ((F.mapHomologicalComplex (.up ℤ)).map f)) :=
  boundedAboveLeftDerivedModelIso F _ (P.cone Q f) ≪≫
    DerivedCategory.Q.mapIso (CochainComplex.mappingCone.mapHomologicalComplexIso f F)

/-- The derived cone computation preserves its standard right inclusion. -/
lemma boundedAboveLeftDerivedConeIso_inr [EnoughProjectives C] (F : C ⥤ E) [F.Additive]
    {X : DerivedCategory C} {Y : DerivedCategory.Minus C}
    (P : BoundedAboveDerivedModel X) (Q : BoundedAboveDerivedModel Y.obj)
    (f : P.complex ⟶ Q.complex) :
    ((boundedAboveLeftDerived F).map (boundedAboveDerivedConeInr P Q f)).hom ≫
        (boundedAboveLeftDerivedConeIso F P Q f).hom =
      (boundedAboveLeftDerivedModelIso F Y Q).hom ≫ DerivedCategory.Q.map
        (CochainComplex.mappingCone.inr ((F.mapHomologicalComplex (.up ℤ)).map f)) := by
  have hn := boundedAboveLeftDerivedModelIso_naturality F Q (P.cone Q f)
    (boundedAboveDerivedConeInr P Q f) (CochainComplex.mappingCone.inr f) (by
      simp [BoundedAboveDerivedModel.cone, boundedAboveDerivedConeInr])
  simp only [boundedAboveLeftDerivedConeIso, Iso.trans_hom, Functor.mapIso_hom]
  rw [← Category.assoc, hn, Category.assoc]
  congr 1
  rw [← CategoryTheory.Functor.map_comp, CochainComplex.mappingCone.map_inr]

end SerrePositivity

end BoundedAboveDerivedConePart

section BoundedAboveDerivedConeTrianglePart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits HomologicalComplex Pretriangulated
attribute [local instance] HasDerivedCategory.standard
variable {C : Type u} [Category.{v} C] [Abelian C]
variable {E : Type u'} [Category.{v'} E] [Abelian E]

/-- The standard cone projection, using the actual shift inside the bounded-above category. -/
def boundedAboveDerivedConeProjection {X : DerivedCategory.Minus C} {Y : DerivedCategory C}
    (P : BoundedAboveDerivedModel X.obj) (Q : BoundedAboveDerivedModel Y)
    (f : P.complex ⟶ Q.complex) : boundedAboveDerivedConeObject P Q f ⟶ X⟦(1 : ℤ)⟧ :=
  ObjectProperty.homMk (DerivedCategory.Q.map (CochainComplex.mappingCone.triangle f).mor₃ ≫
    (P.shiftMinus 1).iso.hom)

/-- Computing the third cone morphism preserves the mapped cone projection and its shift. -/
lemma boundedAboveLeftDerivedConeIso_projection_model [EnoughProjectives C]
    (F : C ⥤ E) [F.Additive] {X : DerivedCategory.Minus C} {Y : DerivedCategory C}
    (P : BoundedAboveDerivedModel X.obj) (Q : BoundedAboveDerivedModel Y)
    (f : P.complex ⟶ Q.complex) :
    ((boundedAboveLeftDerived F).map (boundedAboveDerivedConeProjection P Q f)).hom ≫
        (boundedAboveLeftDerivedModelIso F (X⟦(1 : ℤ)⟧) (P.shiftMinus 1)).hom ≫
        DerivedCategory.Q.map
          (((F.mapHomologicalComplex (.up ℤ)).commShiftIso (1 : ℤ)).app P.complex).hom ≫
        (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app
          ((F.mapHomologicalComplex (.up ℤ)).obj P.complex) =
      (boundedAboveLeftDerivedConeIso F P Q f).hom ≫
        DerivedCategory.Q.map (CochainComplex.mappingCone.triangle
          ((F.mapHomologicalComplex (.up ℤ)).map f)).mor₃ ≫
        (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app
          ((F.mapHomologicalComplex (.up ℤ)).obj P.complex) := by
  have hn := boundedAboveLeftDerivedModelIso_naturality F (P.cone Q f) (P.shiftMinus 1)
    (boundedAboveDerivedConeProjection P Q f) (CochainComplex.mappingCone.triangle f).mor₃
    (by simp [BoundedAboveDerivedModel.cone, boundedAboveDerivedConeProjection])
  have hδ : (F.mapHomologicalComplex (.up ℤ)).map
      (CochainComplex.mappingCone.triangle f).mor₃ ≫
        (((F.mapHomologicalComplex (.up ℤ)).commShiftIso (1 : ℤ)).app P.complex).hom =
      (CochainComplex.mappingCone.mapHomologicalComplexIso f F).hom ≫
        (CochainComplex.mappingCone.triangle ((F.mapHomologicalComplex (.up ℤ)).map f)).mor₃ :=
    CochainComplex.mappingCone.map_δ f F
  simp only [boundedAboveLeftDerivedConeIso, Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
  rw [← Category.assoc, hn]
  simp only [Category.assoc]
  congr 1
  rw [← Category.assoc, ← CategoryTheory.Functor.map_comp, hδ,
    CategoryTheory.Functor.map_comp]
  simp only [Category.assoc]

/-- The chosen-model cone projection is compatible with the canonical derived shift comparison. -/
lemma boundedAboveLeftDerivedConeIso_projection [EnoughProjectives C]
    (F : C ⥤ E) [F.Additive] (X : DerivedCategory.Minus C) {Y : DerivedCategory C}
    (Q : BoundedAboveDerivedModel Y) (f : (boundedAboveDerivedChosenModel X).complex ⟶ Q.complex) :
    ((boundedAboveLeftDerived F).map
        (boundedAboveDerivedConeProjection (boundedAboveDerivedChosenModel X) Q f)).hom ≫
        (boundedAboveLeftDerivedShiftIso F X 1).hom ≫
        (boundedAboveLeftDerivedModelIso F X (boundedAboveDerivedChosenModel X)).hom⟦(1 : ℤ)⟧' =
      (boundedAboveLeftDerivedConeIso F (boundedAboveDerivedChosenModel X) Q f).hom ≫
        DerivedCategory.Q.map (CochainComplex.mappingCone.triangle
          ((F.mapHomologicalComplex (.up ℤ)).map f)).mor₃ ≫
        (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app
          ((F.mapHomologicalComplex (.up ℤ)).obj (boundedAboveDerivedChosenModel X).complex) := by
  simp only [boundedAboveLeftDerivedShiftIso, id_eq, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom, Category.assoc, ← CategoryTheory.Functor.map_comp,
    Iso.inv_hom_id, CategoryTheory.Functor.map_id]
  erw [Category.comp_id]
  exact boundedAboveLeftDerivedConeIso_projection_model F (boundedAboveDerivedChosenModel X) Q f

/-- The actual left-derived images of a morphism, its cone inclusion and its cone projection. -/
def boundedAboveLeftDerivedConeTriangle [EnoughProjectives C] (F : C ⥤ E) [F.Additive]
    {X Y : DerivedCategory.Minus C} (f : X ⟶ Y) : Triangle (DerivedCategory E) :=
  let P := boundedAboveDerivedChosenModel X
  let Q := boundedAboveDerivedChosenModel Y
  let h := P.map Q f.hom
  Triangle.mk ((boundedAboveLeftDerived F).map f).hom
    ((boundedAboveLeftDerived F).map (boundedAboveDerivedConeInr P Q h)).hom
    (((boundedAboveLeftDerived F).map (boundedAboveDerivedConeProjection P Q h)).hom ≫
      (boundedAboveLeftDerivedShiftIso F X 1).hom)

/-- Compare the actual derived image triangle with the canonical mapped-complex cone triangle. -/
def boundedAboveLeftDerivedConeTriangleIso [EnoughProjectives C] (F : C ⥤ E) [F.Additive]
    {X Y : DerivedCategory.Minus C} (f : X ⟶ Y) :
    boundedAboveLeftDerivedConeTriangle F f ≅
      DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCone.triangle
        ((F.mapHomologicalComplex (.up ℤ)).map
          ((boundedAboveDerivedChosenModel X).map (boundedAboveDerivedChosenModel Y) f.hom))) := by
  let P := boundedAboveDerivedChosenModel X
  let Q := boundedAboveDerivedChosenModel Y
  let h := P.map Q f.hom
  refine Triangle.isoMk _ _ (boundedAboveLeftDerivedModelIso F X P)
    (boundedAboveLeftDerivedModelIso F Y Q) (boundedAboveLeftDerivedConeIso F P Q h) ?_ ?_ ?_
  · exact boundedAboveLeftDerivedModelIso_naturality F P Q f h (P.map_naturality Q f.hom)
  · exact boundedAboveLeftDerivedConeIso_inr F P Q h
  · change (((boundedAboveLeftDerived F).map (boundedAboveDerivedConeProjection P Q h)).hom ≫
      (boundedAboveLeftDerivedShiftIso F X 1).hom) ≫
        (boundedAboveLeftDerivedModelIso F X P).hom⟦(1 : ℤ)⟧' =
      (boundedAboveLeftDerivedConeIso F P Q h).hom ≫
        (DerivedCategory.Q.map (CochainComplex.mappingCone.triangle
          ((F.mapHomologicalComplex (.up ℤ)).map h)).mor₃ ≫
          (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app
            ((F.mapHomologicalComplex (.up ℤ)).obj P.complex))
    simpa only [Category.assoc] using boundedAboveLeftDerivedConeIso_projection F X Q h

/-- The actual left-derived image triangles are distinguished for any additive F. -/
lemma boundedAboveLeftDerivedConeTriangle_distinguished [EnoughProjectives C]
    (F : C ⥤ E) [F.Additive] {X Y : DerivedCategory.Minus C} (f : X ⟶ Y) :
    boundedAboveLeftDerivedConeTriangle F f ∈ distTriang (DerivedCategory E) :=
  isomorphic_distinguished _ (DerivedCategory.mappingCone_triangle_distinguished _) _
    (boundedAboveLeftDerivedConeTriangleIso F f)

end SerrePositivity

end BoundedAboveDerivedConeTrianglePart

section BoundedAboveSourceConeTrianglePart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits HomologicalComplex Pretriangulated
attribute [local instance] HasDerivedCategory.standard
variable {C : Type u} [Category.{v} C] [Abelian C] [EnoughProjectives C]

/-- The cone triangle with the original derived objects as its first two vertices. -/
def boundedAboveSourceConeTriangle {X Y : DerivedCategory.Minus C} (f : X ⟶ Y) :
    Triangle (DerivedCategory C) :=
  let P := boundedAboveDerivedChosenModel X
  let Q := boundedAboveDerivedChosenModel Y
  let h := P.map Q f.hom
  Triangle.mk f.hom (boundedAboveDerivedConeInr P Q h).hom
    ((boundedAboveDerivedConeProjection P Q h).hom ≫
      (DerivedCategory.Minus.ι.commShiftIso (1 : ℤ)).hom.app X)

/-- The source cone triangle agrees with the standard cone of the lifted chain map. -/
def boundedAboveSourceConeTriangleIso {X Y : DerivedCategory.Minus C} (f : X ⟶ Y) :
    boundedAboveSourceConeTriangle f ≅
      DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCone.triangle
        ((boundedAboveDerivedChosenModel X).map (boundedAboveDerivedChosenModel Y) f.hom)) := by
  let P := boundedAboveDerivedChosenModel X
  let Q := boundedAboveDerivedChosenModel Y
  let h := P.map Q f.hom
  refine Triangle.isoMk _ _ P.iso.symm Q.iso.symm (Iso.refl _) ?_ ?_ ?_
  · change f.hom ≫ Q.iso.inv = P.iso.inv ≫ DerivedCategory.Q.map h
    rw [P.map_Q Q f.hom]
    simp
  · simp [boundedAboveSourceConeTriangle, boundedAboveDerivedConeInr, Q]
  · change ((boundedAboveDerivedConeProjection P Q h).hom ≫
      (DerivedCategory.Minus.ι.commShiftIso (1 : ℤ)).hom.app X) ≫
        P.iso.inv⟦(1 : ℤ)⟧' =
      𝟙 _ ≫ (DerivedCategory.Q.map (CochainComplex.mappingCone.triangle h).mor₃ ≫
        (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app P.complex)
    simp [boundedAboveDerivedConeProjection, BoundedAboveDerivedModel.shiftMinus,
      BoundedAboveDerivedModel.transport, BoundedAboveDerivedModel.shift, Category.assoc,
      ← Functor.map_comp]

lemma boundedAboveSourceConeTriangle_distinguished {X Y : DerivedCategory.Minus C}
    (f : X ⟶ Y) : boundedAboveSourceConeTriangle f ∈ distTriang (DerivedCategory C) :=
  isomorphic_distinguished _ (DerivedCategory.mappingCone_triangle_distinguished _) _
    (boundedAboveSourceConeTriangleIso f)

/-- Any distinguished triangle on the same first morphism is isomorphic to the source cone. -/
def boundedAboveSourceConeTriangleIsoOfDistinguished {X Y : DerivedCategory.Minus C}
    (f : X ⟶ Y) (Z : DerivedCategory C) (g : Y.obj ⟶ Z) (δ : Z ⟶ X.obj⟦(1 : ℤ)⟧)
    (hT : Triangle.mk f.hom g δ ∈ distTriang (DerivedCategory C)) :
    boundedAboveSourceConeTriangle f ≅ Triangle.mk f.hom g δ :=
  isoTriangleOfIso₁₂ _ _ (boundedAboveSourceConeTriangle_distinguished f) hT
    (Iso.refl _) (Iso.refl _) (by simp [boundedAboveSourceConeTriangle])

variable {E : Type u'} [Category.{v'} E] [Abelian E]

/-- Apply the actual left derived functor to all three arrows, using its shift comparison. -/
def boundedAboveLeftDerivedTriangle (F : C ⥤ E) [F.Additive]
    {X Y Z : DerivedCategory.Minus C} (f : X ⟶ Y) (g : Y ⟶ Z) (δ : Z ⟶ X⟦(1 : ℤ)⟧) :
    Triangle (DerivedCategory E) :=
  Triangle.mk ((boundedAboveLeftDerived F).map f).hom ((boundedAboveLeftDerived F).map g).hom
    (((boundedAboveLeftDerived F).map δ).hom ≫ (boundedAboveLeftDerivedShiftIso F X 1).hom)

/-- Every bounded-above distinguished triangle gives a distinguished left-derived image. -/
lemma boundedAboveLeftDerivedTriangle_distinguished (F : C ⥤ E) [F.Additive]
    {X Y Z : DerivedCategory.Minus C} (f : X ⟶ Y) (g : Y ⟶ Z) (δ : Z ⟶ X⟦(1 : ℤ)⟧)
    (hT : Triangle.mk f.hom g.hom
      (δ.hom ≫ (DerivedCategory.Minus.ι.commShiftIso (1 : ℤ)).hom.app X) ∈
        distTriang (DerivedCategory C)) :
    boundedAboveLeftDerivedTriangle F f g δ ∈ distTriang (DerivedCategory E) := by
  let P := boundedAboveDerivedChosenModel X
  let Q := boundedAboveDerivedChosenModel Y
  let h := P.map Q f.hom
  let e := boundedAboveSourceConeTriangleIsoOfDistinguished f Z.obj g.hom
    (δ.hom ≫ (DerivedCategory.Minus.ι.commShiftIso (1 : ℤ)).hom.app X) hT
  let k : boundedAboveDerivedConeObject P Q h ≅ Z :=
    ObjectProperty.isoMk _ (Triangle.π₃.mapIso e)
  have hg : boundedAboveDerivedConeInr P Q h ≫ k.hom = g := by
    apply InducedCategory.hom_ext
    have he := e.hom.comm₂
    simpa [e, k, boundedAboveSourceConeTriangleIsoOfDistinguished,
      boundedAboveSourceConeTriangle, P, Q, h] using he
  have hδ : boundedAboveDerivedConeProjection P Q h = k.hom ≫ δ := by
    apply InducedCategory.hom_ext
    apply (cancel_mono ((DerivedCategory.Minus.ι.commShiftIso (1 : ℤ)).hom.app X)).mp
    have he := e.hom.comm₃
    simpa [e, k, boundedAboveSourceConeTriangleIsoOfDistinguished,
      boundedAboveSourceConeTriangle, P, Q, h, Category.assoc] using he
  let ek : ((boundedAboveLeftDerived F).obj (boundedAboveDerivedConeObject P Q h)).obj ≅
      ((boundedAboveLeftDerived F).obj Z).obj :=
    DerivedCategory.Minus.ι.mapIso ((boundedAboveLeftDerived F).mapIso k)
  have ei : boundedAboveLeftDerivedConeTriangle F f ≅
      boundedAboveLeftDerivedTriangle F f g δ := by
    refine Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) ek
      (by simp [boundedAboveLeftDerivedConeTriangle, boundedAboveLeftDerivedTriangle]) ?_ ?_
    · change ((boundedAboveLeftDerived F).map (boundedAboveDerivedConeInr P Q h)).hom ≫
        ((boundedAboveLeftDerived F).map k.hom).hom = 𝟙 _ ≫ _
      rw [← ObjectProperty.FullSubcategory.comp_hom, ← Functor.map_comp, hg, Category.id_comp]
      rfl
    · change (((boundedAboveLeftDerived F).map (boundedAboveDerivedConeProjection P Q h)).hom ≫
        (boundedAboveLeftDerivedShiftIso F X 1).hom) ≫ (𝟙 _)⟦(1 : ℤ)⟧' =
          ((boundedAboveLeftDerived F).map k.hom).hom ≫
            (((boundedAboveLeftDerived F).map δ).hom ≫ _)
      rw [hδ, Functor.map_comp]
      simp [Category.assoc]
  exact isomorphic_distinguished _ (boundedAboveLeftDerivedConeTriangle_distinguished F f) _ ei.symm

end SerrePositivity

end BoundedAboveSourceConeTrianglePart
