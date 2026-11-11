module

public import SerrePositivity.KST.Spectra.EnrichedParameterCylinderFiber
public import SerrePositivity.KST.Spectra.SpectrumCotensorEvaluationNerveFamily
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.HomEnrichedNaturality

/-!
概要：cotensor の評価の族を元の BF 対象へ制限し、全 Hom の普遍評価と照合する。
方針：一対象上の円柱の豊穣関手と nerve の pairing の厳密可換性を使う。
規約：逆同値の選択を介さない共通解像上の式。使われ方：円の評価四角形の極限性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.OmegaSpectrum.CotensorCompatible
local instance evaluationFiberSpectrumSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

/-- 元の一対象上の、二対象のパラメータ円柱から Sp の BF 圏への豊穣評価。 -/
def evaluationFiberEnriched (A : PointedSimplicialSet.{u}) (X : Object A) :
    EnrichedFunctor SSet.{u} (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedParameterCylinderHom.Object A.right
      _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Point.{u + 1}) OmegaSpectrum.{u} :=
  (EnrichedParameterCylinder.fiberEnriched A.right X).comp SSet (evaluationCylinderEnriched A)

/-- 一対象での評価の cross Hom は、元の cotensor の普遍評価そのもの。 -/
lemma evaluationFiber_cross (A : PointedSimplicialSet.{u}) (X : Object A) :
    (ρ_ A.right).inv ≫ (evaluationFiberEnriched A X).map
        (⟨false, ⟨PUnit.unit⟩⟩ : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedParameterCylinderHom.Object A.right
          _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Point.{u + 1}) ⟨true, ⟨PUnit.unit⟩⟩ =
      (cotensorEvaluation A X.val).right := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro a
  change ((evaluationCylinderEnriched A).map
    (⟨false, X⟩ : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedParameterCylinderHom.Object A.right (Object A)) ⟨true, X⟩).app d
      (a, (eId SSet X).app d PUnit.unit) = _
  have h := ConcreteCategory.congr_hom (NatTrans.congr_app (evaluationCylinder_cross A X) d) a
  exact h

/-- 一対象での評価は、全次数のパラメータ単体で元の普遍評価を保持する。 -/
lemma evaluationFiber_cross_app (A : PointedSimplicialSet.{u}) (X : Object A)
    (n : ℕ) (a : A.right _⦋n⦌) :
    ((evaluationFiberEnriched A X).map
      (⟨false, ⟨PUnit.unit⟩⟩ : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedParameterCylinderHom.Object A.right
        _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Point.{u + 1}) ⟨true, ⟨PUnit.unit⟩⟩).app
          (Opposite.op ⦋n⦌) (a, PUnit.unit) =
      (cotensorEvaluation A X.val).right.app (Opposite.op ⦋n⦌) a := by
  have h := ConcreteCategory.congr_hom (NatTrans.congr_app (evaluationFiber_cross A X)
    (Opposite.op ⦋n⦌)) a
  exact h

/-- 共通解像上の評価の族を元の対象へ制限すると、実際の豊穣評価の nerve。 -/
lemma evaluationNerveFamily_fiber (A : PointedSimplicialSet.{u}) (X : Object A) :
    lift (SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex X))
        (𝟙 (SimplicialNerve (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedParameterCylinderHom.Object A.right
          _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Point.{u + 1}))) ≫ evaluationNerveFamily A =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (evaluationFiberEnriched A X) := by
  rw [evaluationNerveFamily, ← Category.assoc, EnrichedParameterCylinder.nervePair_fiber,
    evaluationCylinderInfinityMap, ← _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_comp]
  rfl

/-- 一対象での coherent Hom 比較単体は、元の普遍評価の単体を保持する。 -/
lemma evaluationFiber_comparison (A : PointedSimplicialSet.{u}) (X : Object A)
    (n : ℕ) (a : A.right _⦋n⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonSimplex
        (X := (⟨false, ⟨PUnit.unit⟩⟩ : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedParameterCylinderHom.Object A.right
          _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Point.{u + 1}))
        (Y := ⟨true, ⟨PUnit.unit⟩⟩) (a, PUnit.unit)).comp SSet
          (evaluationFiberEnriched A X) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonSimplex
        ((cotensorEvaluation A X.val).right.app (Opposite.op ⦋n⦌) a) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentHomComparisonSimplex_postcomp, evaluationFiber_cross_app]

end SerrePositivity.KST.Spectra.OmegaSpectrum.CotensorCompatible
