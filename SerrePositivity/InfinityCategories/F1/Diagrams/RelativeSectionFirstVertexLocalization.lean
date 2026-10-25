module

public import SerrePositivity.InfinityCategories.F1.Diagrams.LocalizationRelativeRestriction
public import SerrePositivity.InfinityCategories.F1.Transport.LocalizationAllBases

/-!
概要：一般の初頂点写像に沿う、left fibration への相対関手の制限は同値。
方針：単体圏の初頂点写像の局所化性を、指定底を保つ相対制限へ適用する。
規約：始域は一般の quasicategory であり、標準単体間の射には限定しない。
使われ方：K-B-S の元の全族と元の射影を固定した相対的な降下。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

/-- 一般初頂点写像に沿う相対切断制限は、同じ元の底を保つ同値である。 -/
lemma relativeFunctorPre_isQCatEquivalence_of_firstVertexLocalization
    {A E B : SSet.{u}} [Quasicategory A] [Quasicategory B]
    (p : E ⟶ B) [LeftFibration p] (b : A ⟶ B) :
    IsQCatEquivalence (relativeFunctorPre p b (transportSimplexFirstVertexMap A)) := by
  have : Quasicategory E := quasicategory_of_innerFibration p
  exact (transportSimplexFirstVertexMap_isLocalization A).relativeFunctorPre_isQCatEquivalence p b

end SerrePositivity.InfinityCategories
