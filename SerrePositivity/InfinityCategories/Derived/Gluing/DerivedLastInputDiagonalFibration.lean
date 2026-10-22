module
public import SerrePositivity.InfinityCategories.Derived.Gluing.RestrictedInputDiagonal
public import SerrePositivity.InfinityCategories.Derived.Gluing.DerivedCompositionInputDiagonals

/-! 元の左 Hom 入力を保持する導来合成対応の同じ対角は Kan fibration。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits MonoidalCategory DifferentialGraded SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial

lemma dgGluingLastFixedInputDiagonal_fibration {X A : SSet.{u}} [Quasicategory X]
    [KanComplex A] (x : X _⦋0⦌) {y z : X _⦋0⦌} (g : X.Edge y z)
    (a : A ⟶ intervalMappingSpace x y) :
    Fibration (pullback.fst (compositionCorrespondenceFirst x g) a ≫
      compositionCorrespondenceDiagonal x g) := by
  have : Fibration (CartesianMonoidalCategory.lift (compositionCorrespondenceFirst x g)
      (compositionCorrespondenceDiagonal x g)) := dgGluingCompositionInputDiagonal_fibration x g
  exact dgGluingRestrictedDiagonal_fibration _ _ a

variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)

lemma dgGluingDerivedLastCompositionInputDiagonal_fibration (X Y : DGGluingObject R C D M) :
    Fibration (dgGluingDerivedLastCompositionInputDiagonal R C D M X Y) := by
  exact dgGluingLastFixedInputDiagonal_fibration _ _
    (dgGluingDerivedLeftCoefficientInput R C D M X Y)

end SerrePositivity.InfinityCategories
