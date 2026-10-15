module

public import SerrePositivity.HomotopicalAlgebra.Localization.Minimality

/-! # Iterated localization agrees with localization at the union

Compare actual model structures, including the localization performed
with the first localized model as source. The Quillen universal property
implies minimality, which identifies both weak-equivalence classes and
then all model classes. This does not identify just composite replacement
functors or assume the desired comparison of derived mapping spaces.
-/

@[expose] public section
universe v u
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace SerrePositivity.Bousfield
variable {C : Type u} [Category.{v} C] [original : ModelCategory C]
  [simplicial : ModelCategory SSet.{v}]
  {cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C)}
  {fib : MorphismProperty.FunctorialFactorizationData (trivialCofibrations C) (fibrations C)}
  {S T : MorphismProperty C} {mS mST mI : ModelCategory C}
  (hS : @IsLocalizationModel C _ original simplicial cof fib S mS)
  (hST : @IsLocalizationModel C _ original simplicial cof fib (S ⊔ T) mST)
  (cofS : MorphismProperty.FunctorialFactorizationData mS.categoryWithCofibrations.cofibrations
    (mS.categoryWithFibrations.fibrations ⊓ mS.categoryWithWeakEquivalences.weakEquivalences))
  (fibS : MorphismProperty.FunctorialFactorizationData
    (mS.categoryWithCofibrations.cofibrations ⊓ mS.categoryWithWeakEquivalences.weakEquivalences)
    mS.categoryWithFibrations.fibrations)
  (hI : @IsLocalizationModel C _ mS simplicial cofS fibS T mI)
  (hcof : simplicial.categoryWithCofibrations.cofibrations = MorphismProperty.monomorphisms _)
  (hfib : simplicial.categoryWithFibrations.fibrations = SSet.modelCategoryQuillen.J.{v}.rlp)

include hS hST hI hcof hfib in
lemma iterated_localization_classes :
    mST.categoryWithCofibrations.cofibrations = mI.categoryWithCofibrations.cofibrations ∧
      mST.categoryWithWeakEquivalences.weakEquivalences =
        mI.categoryWithWeakEquivalences.weakEquivalences ∧
      mST.categoryWithFibrations.fibrations = mI.categoryWithFibrations.fibrations := by
  let := original
  have hiW := @IsLocalizationModel.weakEquivalences_eq C _ mS simplicial cofS fibS T mI hI
  have hiC := @IsLocalizationModel.cofibrations_eq C _ mS simplicial cofS fibS T mI hI
  have h0S : original.categoryWithWeakEquivalences.weakEquivalences ≤
      mS.categoryWithWeakEquivalences.weakEquivalences :=
    (weakEquivalences_le_localEquivalences cof fib hcof S).trans hS.weakEquivalences_eq.symm.le
  have h0ST : original.categoryWithWeakEquivalences.weakEquivalences ≤
      mST.categoryWithWeakEquivalences.weakEquivalences :=
    (weakEquivalences_le_localEquivalences cof fib hcof (S ⊔ T)).trans
      hST.weakEquivalences_eq.symm.le
  have hSI : mS.categoryWithWeakEquivalences.weakEquivalences ≤
      mI.categoryWithWeakEquivalences.weakEquivalences :=
    (@weakEquivalences_le_localEquivalences C _ mS simplicial cofS fibS hcof T).trans
      hiW.symm.le
  have hSgen : S ≤ mS.categoryWithWeakEquivalences.weakEquivalences :=
    (generators_le_localEquivalences cof fib S).trans hS.weakEquivalences_eq.symm.le
  have hTgen : T ≤ mI.categoryWithWeakEquivalences.weakEquivalences :=
    (@generators_le_localEquivalences C _ mS simplicial cofS fibS T).trans
      hiW.symm.le
  have hSTgen : S ⊔ T ≤ mST.categoryWithWeakEquivalences.weakEquivalences :=
    (generators_le_localEquivalences cof fib (S ⊔ T)).trans hST.weakEquivalences_eq.symm.le
  have hSTI := hST.identity_leftQuillen_of_contains hcof hfib mI
    (hiC.trans hS.cofibrations_eq) (h0S.trans hSI)
    (sup_le (hSgen.trans hSI) hTgen)
  have hSST := hS.weakEquivalences_le_of_contains hcof hfib mST hST.cofibrations_eq
    h0ST (le_sup_left.trans hSTgen)
  have hIST := hI.identity_leftQuillen_of_contains (original := mS) hcof hfib mST
    (hST.cofibrations_eq.trans hS.cofibrations_eq.symm) hSST (le_sup_right.trans hSTgen)
  exact Quillen.classes_eq_of_identity_leftQuillen_both mST mI hSTI hIST


include hS hST hI hcof hfib in
lemma union_is_iterated_localization :
    @IsLocalizationModel C _ mS simplicial cofS fibS T mST := by
  let := original
  have he := iterated_localization_classes hS hST cofS fibS hI hcof hfib
  have hiC := @IsLocalizationModel.cofibrations_eq C _ mS simplicial cofS fibS T mI hI
  have hiW := @IsLocalizationModel.weakEquivalences_eq C _ mS simplicial cofS fibS T mI hI
  refine @IsLocalizationModel.mk C _ mS simplicial cofS fibS T mST
    (he.1.trans hiC) (he.2.1.trans hiW) (fun Y => ?_)
  exact (congrArg (fun P : MorphismProperty C => P (terminal.from Y)) he.2.2).to_iff.trans
    (@IsLocalizationModel.fibrant_iff C _ mS simplicial cofS fibS T mI hI Y)

end SerrePositivity.Bousfield
