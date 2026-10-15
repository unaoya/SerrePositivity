module

public import SerrePositivity.HomotopicalAlgebra.Localization.ReplacementData

/-! # Homotopy universal property of the actual local-replacement unit

Maps from X to any local target in the ordinary homotopy category extend
uniquely across X → L X. In particular, the two weak idempotence maps agree
in the original homotopy category, not just after another localization.
-/

@[expose] public section
universe v u vH uH
noncomputable section
open CategoryTheory HomotopicalAlgebra
open SerrePositivity.HomotopyFunctionComplex

namespace SerrePositivity.Bousfield
variable {C : Type u} [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
  (fib : MorphismProperty.FunctorialFactorizationData (trivialCofibrations C) (fibrations C))


variable {H : Type uH} [Category.{vH} H] (Q : C ⥤ H)
  [Q.IsLocalization (weakEquivalences C)]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

include hcof hfib in
lemma mappingTest_hom_bijective {X Y Z : C} (f : X ⟶ Y)
    (h : mappingTest cof fib Z f) :
    Function.Bijective (fun k : Q.obj Y ⟶ Q.obj Z => Q.map f ≫ k) := by
  have := chosenMappingSpace_isFibrant cof fib hfib (Opposite.op X) Z
  have := chosenMappingSpace_isFibrant cof fib hfib (Opposite.op Y) Z
  have : WeakEquivalence
      (((HomotopyFunctionComplex.chosenResolutionHom cof fib).map f.op).app Z) := ⟨h⟩
  have hb := SimplicialModel.piZero_bijective_of_weakEquivalence_of_fibrant hcof
    (((HomotopyFunctionComplex.chosenResolutionHom cof fib).map f.op).app Z)
  let eX := HomotopyFunctionComplex.chosenResolutionHomPiZeroEquiv Q cof fib (Opposite.op X) Z
  let eY := HomotopyFunctionComplex.chosenResolutionHomPiZeroEquiv Q cof fib (Opposite.op Y) Z
  have hnat (z) : eX (SSet.mapπ₀
      (((HomotopyFunctionComplex.chosenResolutionHom cof fib).map f.op).app Z) z) =
      Q.map f ≫ eY z :=
    HomotopyFunctionComplex.chosenResolutionHomPiZeroEquiv_naturality_source Q cof fib f.op Z z
  have hb' := eX.bijective.comp (hb.comp eY.symm.bijective)
  simpa only [Function.comp_def, hnat, Equiv.apply_symm_apply] using hb'

namespace LocalReplacementData
variable {cof fib} {S : MorphismProperty C} (d : LocalReplacementData cof fib S)

include hcof hfib in
lemma unit_hom_bijective (X Z : C) (hZ : localObjects cof fib S Z) :
    Function.Bijective (fun k : Q.obj (d.L.obj X) ⟶ Q.obj Z => Q.map (d.η.app X) ≫ k) :=
  mappingTest_hom_bijective cof fib Q hcof hfib _ (d.unit_localEquivalence X Z hZ)

include hcof hfib in
lemma idempotence_coherence (X : C) :
    Q.map (d.L.map (d.η.app X)) = Q.map (d.η.app (d.L.obj X)) := by
  apply (d.unit_hom_bijective Q hcof hfib X (d.L.obj (d.L.obj X))
    (d.localFibrant (d.L.obj X)).2).injective
  simpa only [← Q.map_comp] using congrArg Q.map (d.unit_naturality X)

end LocalReplacementData
end SerrePositivity.Bousfield
