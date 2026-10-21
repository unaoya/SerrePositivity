module

public import SerrePositivity.EInfinity.Hammock.ForwardZigzagDiscrete
public import SerrePositivity.EInfinity.Hammock.BackwardZigzagNativeDiscrete
public import SerrePositivity.EInfinity.Hammock.DiscreteNerveIso
public import SerrePositivity.EInfinity.Hammock.NerveWeakTransport

/-!
# 元の単一列の graph と離散 Hom の弱同値

概要：同じ始終点の元の単一列を評価する。
方針：端点移送と離散圏の nerve の同型を使う。
規約：モデル構造を要求しない。
使われ方：DK5.7の単一列の比較。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.EInfinity.Hammock
open CategoryTheory SerrePositivity.InfinityCategories
variable {C : Type u} [Category.{u} C] {W : MorphismProperty C} [W.IsMultiplicative] {X Y : C}
def ForwardZigzag.graphValue : graph W (Word.single .forward) X Y ⟶
    (Functor.const SimplexCategoryᵒᵖ).obj (X ⟶ Y) :=
  nerveMap toDiscrete ≫ (DiscreteNerve.iso (X ⟶ Y)).hom
lemma ForwardZigzag.graphValue_app (n : SimplexCategoryᵒᵖ)
    (σ : (graph W (Word.single .forward) X Y).obj n) :
    (graphValue.app n) σ = value (σ.obj 0) := rfl
lemma ForwardZigzag.graphValue_weak :
    IsWeakHomotopyEquivalence (graphValue (W := W) (X := X) (Y := Y)) :=
  (nerveMap_equivalence_isWeakHomotopyEquivalence discreteEquivalence).comp
    (isPrecompositionEquivalence_of_iso (DiscreteNerve.iso (X ⟶ Y))).isWeakHomotopyEquivalence

def BackwardZigzag.graphValue : graph W (Word.single .backward) X Y ⟶
    (Functor.const SimplexCategoryᵒᵖ).obj ((⟨Y⟩ : WideSubcategory W) ⟶ ⟨X⟩) :=
  nerveMap nativeDiscreteEquivalence.functor ≫ (DiscreteNerve.iso _).hom
lemma BackwardZigzag.graphValue_app (n : SimplexCategoryᵒᵖ)
    (σ : (graph W (Word.single .backward) X Y).obj n) :
    (graphValue.app n) σ = markedHomEquiv (value (σ.obj 0)) := rfl
lemma BackwardZigzag.graphValue_weak :
    IsWeakHomotopyEquivalence (graphValue (W := W) (X := X) (Y := Y)) :=
  (nerveMap_equivalence_isWeakHomotopyEquivalence nativeDiscreteEquivalence).comp
    (isPrecompositionEquivalence_of_iso (DiscreteNerve.iso _)).isWeakHomotopyEquivalence
end SerrePositivity.EInfinity.Hammock
