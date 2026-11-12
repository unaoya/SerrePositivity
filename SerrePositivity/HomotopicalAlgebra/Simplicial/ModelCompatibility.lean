module
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Basic

public import SerrePositivity.HomotopicalAlgebra.Simplicial.Generators
public import SerrePositivity.HomotopicalAlgebra.Monoidal.ModelCategory
public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.PushoutProduct
public import Mathlib.AlgebraicTopology.SimplicialSet.PushoutProduct

/-! # Monoidal compatibility for the fixed simplicial cofibration and fibration classes

The monomorphism pushout-product statement is unconditional. The model
consequences require a ModelCategory on the fixed scoped mono/Kan classes;
no weak-equivalence class or existence axiom is introduced here.
-/

@[expose] public section
universe u
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomotopicalAlgebra
namespace SerrePositivity.SimplicialModel
open SSet SerrePositivity.Quillen

lemma simplicial_pushoutProduct_mono {A B X Y : SSet.{u}} (i : A ⟶ B) (j : X ⟶ Y)
    [Mono i] [Mono j] (sq : (curriedTensor SSet.{u}).PushoutObjObj i j) : Mono sq.ι := by
  let mid := Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet.{u})
    (Subcomplex.range i).ι j
  let last := Subcomplex.unionProd.pushoutObjObj (Subcomplex.range i) (Subcomplex.range j)
  let ei : Arrow.mk i ≅ Arrow.mk (Subcomplex.range i).ι :=
    Arrow.isoMk (asIso (Subcomplex.toRange i)) (Iso.refl _) (by simp)
  let ej : Arrow.mk j ≅ Arrow.mk (Subcomplex.range j).ι :=
    Arrow.isoMk (asIso (Subcomplex.toRange j)) (Iso.refl _) (by simp)
  let e := (Functor.PushoutObjObj.ι_iso_of_iso_left
    (F := curriedTensor SSet.{u}) (f₂ := Arrow.mk j) sq mid ei).trans
    (Functor.PushoutObjObj.ι_iso_of_iso_right (F := curriedTensor SSet.{u})
      (f₁ := Arrow.mk (Subcomplex.range i).ι) (f₂ := Arrow.mk j)
      (f₂' := Arrow.mk (Subcomplex.range j).ι) mid last ej)
  apply (MorphismProperty.monomorphisms SSet.{u}).arrow_mk_iso_iff e |>.2
  change Mono (Subcomplex.range i |>.unionProd (Subcomplex.range j)).ι
  infer_instance

section Model
variable [ModelCategory SSet.{u}]
  (hCof : cofibrations SSet.{u} = MorphismProperty.monomorphisms SSet.{u})
  (hFib : fibrations SSet.{u} = SSet.modelCategoryQuillen.J.{u}.rlp)

include hFib in
/-- Once the model axioms hold on the fixed classes, their horn left class
is exactly the trivial cofibrations, rather than an additional hypothesis. -/
lemma simplicial_anodyne_eq_trivialCofibrations :
    SSet.anodyneExtensions.{u} = trivialCofibrations SSet.{u} := by
  change SSet.modelCategoryQuillen.J.{u}.rlp.llp = _
  rw [← hFib]
  exact fibrations_llp _

include hCof hFib in
/-- The actual boundary/horn maps generate any model with the specified classes. -/
lemma simplicial_cofibrantlyGenerated :
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{u}
      SSet.modelCategoryQuillen.I.{u} SSet.modelCategoryQuillen.J.{u} where
  smallObjectI := boundaryGenerators_smallObjectArgument
  smallObjectJ := hornGenerators_smallObjectArgument
  rlp_I := by
    rw [← SSet.rlp_monomorphisms, ← hCof]
    exact cofibrations_rlp _
  rlp_J := hFib.symm

include hCof hFib in
lemma simplicial_isQuillenBifunctor : IsQuillenBifunctor (curriedTensor SSet.{u}) := by
  constructor
  · intro A B X Y i j sq hi hj
    let : Mono i := by
      change MorphismProperty.monomorphisms SSet.{u} i
      rw [← hCof]
      exact (HomotopicalAlgebra.cofibration_iff i).1 hi
    let : Mono j := by
      change MorphismProperty.monomorphisms SSet.{u} j
      rw [← hCof]
      exact (HomotopicalAlgebra.cofibration_iff j).1 hj
    have : Mono sq.ι := simplicial_pushoutProduct_mono i j sq
    apply (HomotopicalAlgebra.cofibration_iff _).2
    rw [hCof]
    infer_instance
  · intro A B X Y i j sq hi hj hw
    let : Mono i := by
      change MorphismProperty.monomorphisms SSet.{u} i
      rw [← hCof]
      exact (HomotopicalAlgebra.cofibration_iff i).1 hi
    let : Mono j := by
      change MorphismProperty.monomorphisms SSet.{u} j
      rw [← hCof]
      exact (HomotopicalAlgebra.cofibration_iff j).1 hj
    have ha : SSet.anodyneExtensions sq.ι := by
      rcases hw with hiw | hjw
      · apply SSet.anodyneExtensions_pushoutObjObjι' sq
        rw [simplicial_anodyne_eq_trivialCofibrations hFib]
        exact ⟨(HomotopicalAlgebra.cofibration_iff i).1 hi, (weakEquivalence_iff i).1 hiw⟩
      · apply SSet.anodyneExtensions_pushoutObjObjι sq
        rw [simplicial_anodyne_eq_trivialCofibrations hFib]
        exact ⟨(HomotopicalAlgebra.cofibration_iff j).1 hj, (weakEquivalence_iff j).1 hjw⟩
    rw [simplicial_anodyne_eq_trivialCofibrations hFib] at ha
    exact (weakEquivalence_iff _).2 ha.2

include hCof hFib in
lemma simplicial_monoidalModel : MonoidalModelCategory SSet.{u} := by
  let : IsCofibrant (𝟙_ SSet.{u}) := by
    constructor
    rw [hCof]
    infer_instance
  exact ⟨simplicial_isQuillenBifunctor hCof hFib, unitAxiom_of_cofibrant_unit _⟩

include hCof hFib in
lemma simplicial_SM7 :
    HasQuillenPullbackHom (MonoidalClosed.internalHom (C := SSet.{u})) :=
  (isQuillenBifunctor_iff_pullbackHom
    (MonoidalClosed.internalHomAdjunction₂ (C := SSet.{u}))).1
      (simplicial_isQuillenBifunctor hCof hFib)

end Model
end SerrePositivity.SimplicialModel
