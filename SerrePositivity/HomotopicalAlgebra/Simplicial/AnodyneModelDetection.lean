module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.AnodyneHomotopyLocalization
public import SerrePositivity.HomotopicalAlgebra.Simplicial.ModelCompatibility
public import SerrePositivity.HomotopicalAlgebra.Quillen.Saturation

/-! # Anodyne inversion agrees with the original weak equivalences in the small model

A trivial fibration has a section. Monomorphisms are cofibrations, so the
section of a trivial fibration is anodyne. Thus anodyne inversion already
inverts all original model weak equivalences; the converse uses saturation.
-/

@[expose] public section
universe v vH uH
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace SerrePositivity.SimplicialModel.AnodyneHomotopy
variable [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  {H : Type uH} [Category.{vH} H] (L : SSet.{v} ⥤ H)
  (hL : SSet.anodyneExtensions.IsInvertedBy L)

include hcof hfib hL in
lemma inverts_model_weakEquivalences : (weakEquivalences SSet.{v}).IsInvertedBy L := by
  intro X Y f hf
  let d := MorphismProperty.factorizationData (cofibrations SSet.{v})
    (trivialFibrations SSet.{v}) f
  have hiw : weakEquivalences SSet.{v} d.i :=
    (weakEquivalences SSet.{v}).of_postcomp _ _ d.hp.2 (d.fac.symm ▸ hf)
  have hi : SSet.anodyneExtensions d.i := by
    rw [simplicial_anodyne_eq_trivialCofibrations hfib]
    exact ⟨d.hi, hiw⟩
  have : Cofibration (initial.to Y) := by
    constructor
    rw [hcof]
    infer_instance
  have : Fibration d.p := ⟨d.hp.1⟩
  have : WeakEquivalence d.p := ⟨d.hp.2⟩
  let sq : CommSq (initial.to d.Z) (initial.to Y) d.p (𝟙 Y) :=
    ⟨by apply initial.hom_ext⟩
  let s := sq.lift
  have hs : s ≫ d.p = 𝟙 Y := sq.fac_right
  have : Mono s := mono_of_mono_fac hs
  have hsw : weakEquivalences SSet.{v} s :=
    (weakEquivalences SSet.{v}).of_postcomp _ _ d.hp.2
      (hs.symm ▸ (weakEquivalences SSet.{v}).id_mem Y)
  have hsc : cofibrations SSet.{v} s :=
    (congrArg (fun W : MorphismProperty SSet.{v} => W s) hcof).mpr inferInstance
  have hsa : SSet.anodyneExtensions s := by
    rw [simplicial_anodyne_eq_trivialCofibrations hfib]
    exact ⟨hsc, hsw⟩
  have : IsIso (L.map s) := hL _ hsa
  have : IsIso (L.map d.p) := (isIso_comp_left_iff (L.map s) _).mp
    (((L.map_comp _ _).symm.trans ((congrArg L.map hs).trans (L.map_id Y))).symm ▸
      inferInstanceAs (IsIso (𝟙 (L.obj Y))))
  have : IsIso (L.map d.i) := hL _ hi
  rw [← d.fac, L.map_comp]
  infer_instance

include hcof hfib in
lemma model_weak_inversion_iff :
    (weakEquivalences SSet.{v}).IsInvertedBy L ↔ SSet.anodyneExtensions.IsInvertedBy L := by
  constructor
  · intro h X Y f hf
    rw [simplicial_anodyne_eq_trivialCofibrations hfib] at hf
    exact h f hf.2
  · intro h
    exact inverts_model_weakEquivalences hcof hfib L h

include hcof hfib in
/-- In the supplied original-universe model, the criterion detects exactly its weak class. -/
lemma weakEquivalences_iff_anodyneQ_isIso {X Y : SSet.{v}} (f : X ⟶ Y) :
    weakEquivalences SSet.{v} f ↔ IsIso (anodyneQ.map f) := by
  constructor
  · exact inverts_model_weakEquivalences hcof hfib anodyneQ
      (Localization.inverts anodyneQ SSet.anodyneExtensions) f
  · intro hf
    let Q := (weakEquivalences SSet.{v}).Q
    have hQ : SSet.anodyneExtensions.IsInvertedBy Q :=
      (model_weak_inversion_iff hcof hfib Q).mp
        (Localization.inverts Q (weakEquivalences SSet.{v}))
    exact (SerrePositivity.Quillen.weakEquivalences_iff_isIso_map Q f).mpr
      (map_isIso_of_anodyneQ_isIso Q hQ f hf)

include hcof hfib in
lemma homotopy_retraction_weakEquivalence {X Y : SSet.{v}} (f : X ⟶ Y) (s : Y ⟶ X)
    (hs : s ≫ f = 𝟙 Y) (h : SSet.Homotopy (𝟙 X) (f ≫ s)) :
    weakEquivalences SSet.{v} f := by
  let e := mapRetractionIso anodyneQ (Localization.inverts anodyneQ SSet.anodyneExtensions)
    f s hs h
  exact (weakEquivalences_iff_anodyneQ_isIso hcof hfib f).mpr
    (inferInstanceAs (IsIso e.hom))

end SerrePositivity.SimplicialModel.AnodyneHomotopy
