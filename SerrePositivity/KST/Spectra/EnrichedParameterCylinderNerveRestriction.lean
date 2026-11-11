module

public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedParameterCylinderPairRestriction
public import SerrePositivity.KST.Spectra.EnrichedParameterCylinderNervePair

/-!
概要：coherent nerve の pairing と、二対象の円柱のパラメータ制限の厳密可換性。
方針：各単体で豊穣関手の制限の式を使う。
規約：全ての高次単体に対する射の等式。使われ方：Sp の評価の族の境界検査。
-/

@[expose] public section
noncomputable section
universe u v
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.EnrichedParameterCylinder

/-- 二対象の円柱のパラメータ制限は、一般の円柱の nerve の制限と可換。 -/
lemma nervePair_restriction {A B : SSet.{u}} {C : Type v}
    [Category.{u} C] [SimplicialCategory C] (i : A ⟶ B) :
    (𝟙 (SimplicialNerve C) ⊗ₘ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.restriction (C := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Point.{v}) i)) ≫
        nervePair (C := C) B =
      nervePair A ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.restriction (C := C) i) := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  rintro ⟨F, G⟩
  exact _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.pairFunctor_restriction i F G

end SerrePositivity.KST.Spectra.EnrichedParameterCylinder
