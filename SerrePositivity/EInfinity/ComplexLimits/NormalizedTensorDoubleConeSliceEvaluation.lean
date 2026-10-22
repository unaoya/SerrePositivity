module
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorDoubleConeSlicePrismProjection
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorConeFamily
public import SerrePositivity.InfinityCategories.Derived.SliceEvaluationPinched

/-!
概要：構成した実 slice 図式の普遍評価を、元の frame 図式から同じ X への全族にする。
方針：同じ普遍評価ホモトピーを全図式で制限し、元の射影の等式で始域を合わせる。
規約：通常 augmentation の円柱との同定は別に検証する。使われ方：大域合成三角形。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories DGNerve
open scoped Simplicial
variable (A : Type u) [CommRing A] (X Y : Complex A)

def normalizedTensorDoubleConeSliceEvaluationHomotopy :
    SSet.Homotopy (normalizedTensorElementNerveDiagram A X Y)
      (SSet.const ((dgNerve.vertexEquiv A (Complex A)).symm X)) where
  h := (functorHomotopyPrecomp
    (roofSliceEvaluationHomotopy ((dgNerve.vertexEquiv A (Complex A)).symm X))
    (normalizedTensorDoubleConeOverDiagram A X Y)).h
  h₀ := by
    rw [SSet.Homotopy.h₀]
    change normalizedTensorDoubleConeOverDiagram A X Y ≫
      sliceOverProjection (normalizedTensorConePoint A X) =
        normalizedTensorElementNerveDiagram A X Y
    exact normalizedTensorDoubleConeOverDiagram_projection A X Y
  h₁ := by
    rw [SSet.Homotopy.h₁, SSet.comp_const]
    rfl
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    exact False.elim s.1.property

lemma normalizedTensorDoubleConeSliceEvaluationHomotopy_h :
    (normalizedTensorDoubleConeSliceEvaluationHomotopy A X Y).h =
      (β_ (nerve (normalizedTensorElementIndex A X Y)) (Δ[1] : SSet.{u + 1})).hom ≫
        rightMappingSpacePrism _ ≫ sliceOverUncurry (normalizedTensorDoubleConeOverDiagram A X Y) :=
  roofSliceEvaluationHomotopy_precomp_h _ _

def normalizedTensorDoubleConeSliceEvaluationHom :
    FunctorHom (normalizedTensorElementNerveDiagram A X Y)
      (SSet.const ((dgNerve.vertexEquiv A (Complex A)).symm X)) :=
  SSet.Truncated.HomotopyCategory.homMk
    (functorEdgeOfSimplicialHomotopy (normalizedTensorDoubleConeSliceEvaluationHomotopy A X Y))

end SerrePositivity.EInfinity.ComplexLimits
