module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictDiagramFreeArrowAugmentationWeak
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictDiagramFreeArrowRealizedAugmentation

/-!
概要：同じ自由arrow frameの実増大射は、全余単体次数で弱同値。
方針：次数零の同定と自然性を用い、両frameの構造射の弱同値性で移す。
使われ方：HTT 4.2.4.4、RR02(a)の実写像空間比較。
規約：増大射もsource frameも既存の指定したものを使う。
-/

@[expose] public noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable (A : Type u) [CommRing A] (d : StrictDiagramDirection)
local instance : ModelCategory (StrictComplexDiagram A d) := strictDiagramReedyModelCategory A d
local instance : HasColimitsOfSize.{u, u} (Complex A) :=
  ⟨fun _ _ => HomologicalComplex.instHasColimitsOfShape⟩
local instance : ∀ (i j : strictDiagramIndex d),
    HasCoproductsOfShape (i ⟶ j) (Complex A) :=
  fun _ _ => HomologicalComplex.instHasColimitsOfShape

/-- 次数零の実増大射は、元のBK増大射の弱同値を保つ。 -/
lemma strictDiagramFreeArrowRealizedAugmentation_zero_weak (X : StrictComplexDiagram A d) :
    weakEquivalences (StrictComplexDiagram A d)
      ((strictDiagramFreeArrowRealizedAugmentation A d X).app (SimplexCategory.mk 0)) := by
  rw [← strictDiagramFreeArrowRealizedAugmentation_zero]
  exact (weakEquivalences (StrictComplexDiagram A d)).comp_mem _ _
    ((weakEquivalences (StrictComplexDiagram A d)).of_isIso
      (strictDiagramFreeArrowRealizedZeroIso A d X).hom)
    (strictDiagramFreeArrowRealizationAugmentation_weak A d X)

/-- 自然性と二つのframeの構造射から、同じ増大射の全次数の弱同値を得る。 -/
lemma strictDiagramFreeArrowRealizedAugmentation_weak (X : StrictComplexDiagram A d)
    (n : SimplexCategory) :
    weakEquivalences (StrictComplexDiagram A d)
      ((strictDiagramFreeArrowRealizedAugmentation A d X).app n) := by
  let f := SimplexCategory.isTerminalZero.from n
  apply (weakEquivalences (StrictComplexDiagram A d)).of_postcomp _ _
    ((strictDiagramSourceFrame A d X).homotopicallyConstant f)
  rw [← (strictDiagramFreeArrowRealizedAugmentation A d X).naturality f]
  exact (weakEquivalences (StrictComplexDiagram A d)).comp_mem _ _
    (strictDiagramFreeArrowRealizedFrame_homotopicallyConstant A d X f)
    (strictDiagramFreeArrowRealizedAugmentation_zero_weak A d X)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
