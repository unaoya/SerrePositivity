module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful

/-! # 単一次数の導来対象とそのホモロジーによる表示 -/

@[expose] public section

universe w

namespace SerrePositivity

open CategoryTheory CategoryTheory.Limits

variable {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory.{w} A]

/-- 単一次数の導来対象は、その次数のホモロジーを置いた対象に同型。 -/
noncomputable def derivedPureHomologyIso (X : DerivedCategory A) (q : ℤ)
    [X.IsGE q] [X.IsLE q] :
    X ≅ (DerivedCategory.singleFunctor A q).obj
      ((DerivedCategory.homologyFunctor A q).obj X) := Classical.choice (by
  obtain ⟨M, ⟨e⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE X q
  let h : (DerivedCategory.homologyFunctor A q).obj X ≅ M :=
    (DerivedCategory.homologyFunctor A q).mapIso e ≪≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso A q).app M
  exact ⟨e ≪≫ (DerivedCategory.singleFunctor A q).mapIso h.symm⟩)

end SerrePositivity
