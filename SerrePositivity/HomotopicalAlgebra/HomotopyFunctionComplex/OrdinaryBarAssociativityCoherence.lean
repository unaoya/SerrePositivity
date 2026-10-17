module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarTripleComparison
public import SerrePositivity.HomotopicalAlgebra.Simplicial.KanComparisonSquare

/-! # A threefold native composite has a specified associativity disc

Four original comparison triangles are retained by two tetrahedra with
one common diagonal. The four boundary intervals are the original two
outer composition comparisons and the two original inner comparisons
composed with the remaining descended map at its fixed endpoint.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonoidalClosed
open SerrePositivity.SimplicialModel

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryBarAssociativityCoherence
open OrdinaryBarFreeResolutionSeed OrdinaryBarRetractSystem OrdinaryBarRelativeHomDescent
open OrdinaryBarTripleComparison
variable {C : Type u} [Category.{v} C] {W X Y Z : D C}
variable [HomotopicalAlgebra.ModelCategory C] [HomotopicalAlgebra.ModelCategory SSet.{v}]
  (hcof : HomotopicalAlgebra.cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : HomotopicalAlgebra.fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (P : SSet.{max u v}) {T : SSet.{v}}
  (j : UniverseLift.obj.{max u v} T ⟶ P)
  (f : UniverseLift.obj.{max u v} T ⟶ OrdinaryBarFixedWordResolution.hom C W X)
  (g : UniverseLift.obj.{max u v} T ⟶ OrdinaryBarFixedWordResolution.hom C X Y)
  (h : UniverseLift.obj.{max u v} T ⟶ OrdinaryBarFixedWordResolution.hom C Y Z)
  (c₀₁ : UniverseLift.obj.{max u v} T ⟶ choices hcof hfib P W X)
  (c₁₂ : UniverseLift.obj.{max u v} T ⟶ choices hcof hfib P X Y)
  (c₂₃ : UniverseLift.obj.{max u v} T ⟶ choices hcof hfib P Y Z)
  (c₀₂ : UniverseLift.obj.{max u v} T ⟶ choices hcof hfib P W Y)
  (c₁₃ : UniverseLift.obj.{max u v} T ⟶ choices hcof hfib P X Z)
  (c₀₃ : UniverseLift.obj.{max u v} T ⟶ choices hcof hfib P W Z)

local notation "R" => nativeRestrictionComparison hcof hfib P j
local notation "N" => OrdinaryBarDiagonalClosedAction.nativeFamily hcof hfib P j
local notation "D" => nativeFamily hcof hfib P j
local notation "sW" => small hcof hfib W
local notation "sX" => small hcof hfib X
local notation "sY" => small hcof hfib Y
local notation "sZ" => small hcof hfib Z

local notation "F₀" => root hcof hfib P j f g h c₀₃
local notation "F₁" => leftIntermediate hcof hfib P j f g h c₂₃ c₀₂
local notation "F₂" => total hcof hfib P j f g h c₀₁ c₁₂ c₂₃
local notation "F₃" => rightIntermediate hcof hfib P j f g h c₀₁ c₁₃
local notation "a" => leftOuterTriangle hcof hfib P j f g h c₂₃ c₀₂ c₀₃
local notation "b" => leftInnerTriangle hcof hfib P j f g h c₀₁ c₁₂ c₂₃ c₀₂
local notation "c" => rightOuterTriangle hcof hfib P j f g h c₀₁ c₁₃ c₀₃
local notation "d" => rightInnerTriangle hcof hfib P j f g h c₀₁ c₁₂ c₂₃ c₁₃

abbrev data : KanComparisonSquare.Filler F₀ F₁ F₂ F₃ a b c d :=
  KanComparisonSquare.build F₀ F₁ F₂ F₃ a b c d
    (SimplexParameterHom.native_kan sW sZ (OrdinaryBarSmallReference.value_kan hcof hfib Z))

abbrev left : T ⊗ SSet.stdSimplex.obj (SimplexCategory.mk 2) ⟶ (ihom sW).obj sZ :=
  KanComparisonSquare.left F₀ F₁ F₂ F₃ a b c d
    (data hcof hfib P j f g h c₀₁ c₁₂ c₂₃ c₀₂ c₁₃ c₀₃)

abbrev right : T ⊗ SSet.stdSimplex.obj (SimplexCategory.mk 2) ⟶ (ihom sW).obj sZ :=
  KanComparisonSquare.right F₀ F₁ F₂ F₃ a b c d
    (data hcof hfib P j f g h c₀₁ c₁₂ c₂₃ c₀₂ c₁₃ c₀₃)

lemma left_first : T ◁ SSet.stdSimplex.δ (2 : Fin 3) ≫
    left hcof hfib P j f g h c₀₁ c₁₂ c₂₃ c₀₂ c₁₃ c₀₃ =
      (nativeCompositionComparison hcof hfib P j (wordComp f g) h c₀₂ c₂₃ c₀₃).h :=
  KanComparisonSquare.left_first F₀ F₁ F₂ F₃ a b c d
    (data hcof hfib P j f g h c₀₁ c₁₂ c₂₃ c₀₂ c₁₃ c₀₃)

lemma left_second : T ◁ SSet.stdSimplex.δ (0 : Fin 3) ≫
    left hcof hfib P j f g h c₀₁ c₁₂ c₂₃ c₀₂ c₁₃ c₀₃ =
      lift (nativeCompositionComparison hcof hfib P j f g c₀₁ c₁₂ c₀₂).h
        (fst T HomotopyBinarySquare.interval ≫
          D (h ≫ OrdinaryBarDiagonalHomAugmentation.smallAugmentation C Y Z) c₂₃) ≫
            MonoidalClosed.comp sW sY sZ := by
  calc
    _ = (KanComparisonTriangle.comparison F₁ F₂ b).h :=
      KanComparisonSquare.left_second F₀ F₁ F₂ F₃ a b c d
        (data hcof hfib P j f g h c₀₁ c₁₂ c₂₃ c₀₂ c₁₃ c₀₃)
    _ = _ := ComparisonTriangleBinary.right_comparison
      (R (wordComp f g) c₀₂) (compositionComparison hcof hfib P j f g c₀₁ c₁₂)
      (R h c₂₃) (MonoidalClosed.comp sW sY sZ)
      (compositionTriangle hcof hfib P j f g c₀₁ c₁₂ c₀₂)

lemma right_first : T ◁ SSet.stdSimplex.δ (2 : Fin 3) ≫
    right hcof hfib P j f g h c₀₁ c₁₂ c₂₃ c₀₂ c₁₃ c₀₃ =
      (nativeCompositionComparison hcof hfib P j f (wordComp g h) c₀₁ c₁₃ c₀₃).h := by
  calc
    _ = (KanComparisonTriangle.comparison F₀ F₃ c).h :=
      KanComparisonSquare.right_first F₀ F₁ F₂ F₃ a b c d
        (data hcof hfib P j f g h c₀₁ c₁₂ c₂₃ c₀₂ c₁₃ c₀₃)
    _ = _ := by
      change uncurry (SSet.stdSimplex.δ (2 : Fin 3) ≫
        (rightOuterTriangle hcof hfib P j f g h c₀₁ c₁₃ c₀₃).triangle) =
          uncurry (SSet.stdSimplex.δ (2 : Fin 3) ≫
            (compositionTriangle hcof hfib P j f (wordComp g h) c₀₁ c₁₃ c₀₃).triangle)
      rfl

lemma right_second : T ◁ SSet.stdSimplex.δ (0 : Fin 3) ≫
    right hcof hfib P j f g h c₀₁ c₁₂ c₂₃ c₀₂ c₁₃ c₀₃ =
      lift (fst T HomotopyBinarySquare.interval ≫
        D (f ≫ OrdinaryBarDiagonalHomAugmentation.smallAugmentation C W X) c₀₁)
        (nativeCompositionComparison hcof hfib P j g h c₁₂ c₂₃ c₁₃).h ≫
          MonoidalClosed.comp sW sX sZ := by
  calc
    _ = (KanComparisonTriangle.comparison F₃ F₂ d).h :=
      KanComparisonSquare.right_second F₀ F₁ F₂ F₃ a b c d
        (data hcof hfib P j f g h c₀₁ c₁₂ c₂₃ c₀₂ c₁₃ c₀₃)
    _ = _ := ComparisonTriangleBinary.left_comparison (MonoidalClosed.comp sW sX sZ) (R f c₀₁)
      (R (wordComp g h) c₁₃) (compositionComparison hcof hfib P j g h c₁₂ c₂₃)
      (compositionTriangle hcof hfib P j g h c₁₂ c₂₃ c₁₃)

lemma common_diagonal : T ◁ SSet.stdSimplex.δ (1 : Fin 3) ≫
    left hcof hfib P j f g h c₀₁ c₁₂ c₂₃ c₀₂ c₁₃ c₀₃ =
      T ◁ SSet.stdSimplex.δ (1 : Fin 3) ≫
        right hcof hfib P j f g h c₀₁ c₁₂ c₂₃ c₀₂ c₁₃ c₀₃ :=
  KanComparisonSquare.common_diagonal F₀ F₁ F₂ F₃ a b c d
    (data hcof hfib P j f g h c₀₁ c₁₂ c₂₃ c₀₂ c₁₃ c₀₃)

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarAssociativityCoherence
