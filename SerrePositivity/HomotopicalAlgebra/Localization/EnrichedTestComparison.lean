module

public import SerrePositivity.HomotopicalAlgebra.Enriched.UnitFrame
public import SerrePositivity.HomotopicalAlgebra.Enriched.DerivedMapping
public import SerrePositivity.HomotopicalAlgebra.Localization.FrameTests

/-! # V-valued derived mapping tests imply ordinary RMap tests

The action unit axiom constructs actual ordinary source frames from a
resolved unit of V. The Hom adjunction compares their actual simplicial
maps with cosimplicial Hom in V. Brown invariance in the fibrant target
then transports V-weak equivalences to the ordinary mapping tests.
-/

@[expose] public section
universe vV uV vC uC
noncomputable section
open CategoryTheory HomotopicalAlgebra
open SerrePositivity.HomotopyFunctionComplex SerrePositivity.Reedy

namespace SerrePositivity.Bousfield
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [ModelCategory V]
  {C : Type uC} [Category.{vC} C] [ModelCategory C] [EnrichedOrdinaryCategory V C]
  (P : SerrePositivity.Enriched.TensorCotensor V C)
  [Quillen.IsQuillenBifunctor P.tensor] [SerrePositivity.Enriched.HasTensorUnitAxiom P]
  (cofV : MorphismProperty.FunctorialFactorizationData (cofibrations V) (trivialFibrations V))
  (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
  (fib : MorphismProperty.FunctorialFactorizationData (trivialCofibrations C) (fibrations C))
  [ModelCategory SSet.{vC}] [ModelCategory SSet.{vV}] [ModelCategory SSet.{max vC vV}]
  (hcofC : cofibrations SSet.{vC} = MorphismProperty.monomorphisms _)
  (hfibC : fibrations SSet.{vC} = SSet.modelCategoryQuillen.J.{vC}.rlp)
  (hcofV : cofibrations SSet.{vV} = MorphismProperty.monomorphisms _)
  (hfibV : fibrations SSet.{vV} = SSet.modelCategoryQuillen.J.{vV}.rlp)
  (hcofB : cofibrations SSet.{max vC vV} = MorphismProperty.monomorphisms _)
  (hfibB : fibrations SSet.{max vC vV} = SSet.modelCategoryQuillen.J.{max vC vV}.rlp)

include P cofV hcofC hfibC hcofV hfibV hcofB hfibB in
lemma mappingTest_of_enrichedTest {X Z : C} (f : X ⟶ Z) (Y : C)
    (hf : weakEquivalences V
      (((SerrePositivity.Enriched.derivedHom (V := V) cof fib).map f.op).app Y)) :
    mappingTest.{vC, uC} (C := C) cof fib Y f := by
  obtain ⟨U, q, hU⟩ := SerrePositivity.Enriched.HasTensorUnitAxiom.exists_replacement (P := P)
  let p := SerrePositivity.Enriched.UnitFrame.asFrame P cofV cof U q hU
  let A := SerrePositivity.Enriched.UnitFrame.diagram cofV U
  let Q := cofibrantSource cof
  let R := fibrantTarget fib
  let g := ((eHomFunctor V C).map (Q.map f).op).app (R.obj Y)
  have : IsCofibrant (Q.obj X) := cofibrantSource_isCofibrant cof X
  have : IsCofibrant (Q.obj Z) := cofibrantSource_isCofibrant cof Z
  have : IsFibrant (R.obj Y) := fibrantTarget_isFibrant fib Y
  have : IsFibrant (((eHomFunctor V C).obj (Opposite.op (Q.obj X))).obj (R.obj Y)) :=
    SerrePositivity.Enriched.mapping_isFibrant P _ _
  have : IsFibrant (((eHomFunctor V C).obj (Opposite.op (Q.obj Z))).obj (R.obj Y)) :=
    SerrePositivity.Enriched.mapping_isFibrant P _ _
  have : WeakEquivalence g := ⟨hf⟩
  have hv := cosimplicialHom_weakEquivalence_of_fibrant hcofV A
    ((cosimplicialResolutionFamily cofV).cofibrant U) g
  have hc := (EnrichedTensorFrame.weakEquivalence_iff P A hcofC hfibC hcofV hfibV
    hcofB hfibB (Q.map f) (R.obj Y)).mpr hv
  exact (mappingTest_eq_of_frame cof fib hcofC p Y).symm.le f hc

include P cofV hcofC hfibC hcofV hfibV hcofB hfibB in
lemma localObjects_of_enrichedLocalObjects (S : MorphismProperty C) (Y : C)
    (hY : SerrePositivity.Enriched.localObjects (V := V) cof fib S Y) :
    localObjects.{vC, uC} (C := C) cof fib S Y := by
  intro X Z f hf
  exact mappingTest_of_enrichedTest P cofV cof fib hcofC hfibC hcofV hfibV hcofB hfibB f Y
    (hY f hf)

end SerrePositivity.Bousfield
