module

public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedParameterCylinderPairFunctor
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.NervePostcomposition

/-!
概要：元の coherent nerve と二対象の円柱の nerve の積から、一般の円柱の nerve への写像。
方針：各単体の二つの豊穣図式を pairing し、前合成との厳密可換性で自然性を示す。
規約：局所 Kan 性は不要。使われ方：Sp の円の評価を全図式の族として扱う。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.EnrichedParameterCylinder
variable (A : SSet.{u}) {C : Type v} [Category.{u} C] [SimplicialCategory C]

/-- 二つの coherent な図式を実際の豊穣円柱へ組み合わせる。 -/
def nervePair :
    SimplicialNerve C ⊗ SimplicialNerve (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedParameterCylinderHom.Object A _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Point.{v}) ⟶ SimplicialNerve (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedParameterCylinderHom.Object A C) where
  app _ := ↾fun ⟨F, G⟩ ↦ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.pairFunctor A F G
  naturality {d e} α := by
    apply ConcreteCategory.hom_ext
    rintro ⟨F, G⟩
    exact _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.pairFunctor_precomp A F G (SimplicialThickening.functor α.unop.toOrderHom.uliftMap)

/-- 二対象の円柱の左端の標準頂点。 -/
def leftVertex : (SimplicialNerve (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedParameterCylinderHom.Object A _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Point.{v})) _⦋0⦌ :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex ⟨false, ⟨PUnit.unit⟩⟩

/-- 二対象の円柱の右端の標準頂点。 -/
def rightVertex : (SimplicialNerve (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedParameterCylinderHom.Object A _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Point.{v})) _⦋0⦌ :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex ⟨true, ⟨PUnit.unit⟩⟩

/-- pairing の左端は元の圏の左端包含そのもの。 -/
lemma nervePair_left :
    lift (𝟙 (SimplicialNerve C)) (SSet.const (leftVertex.{u, v} A)) ≫ nervePair A =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.leftInclusion (C := C) A) := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro F
  apply EnrichedFunctor.ext SSet (fun _ ↦ rfl)
  intro X Y
  change F.map X Y ≫ 𝟙 _ = F.map X Y ≫ 𝟙 _
  rfl

/-- pairing の右端は元の圏の右端包含そのもの。 -/
lemma nervePair_right :
    lift (𝟙 (SimplicialNerve C)) (SSet.const (rightVertex.{u, v} A)) ≫ nervePair A =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.rightInclusion (C := C) A) := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro F
  apply EnrichedFunctor.ext SSet (fun _ ↦ rfl)
  intro X Y
  change F.map X Y ≫ 𝟙 _ = F.map X Y ≫ 𝟙 _
  rfl

end SerrePositivity.KST.Spectra.EnrichedParameterCylinder
