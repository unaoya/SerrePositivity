module
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.GrothendieckKanComparisonCofinality
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.LeftFibrationComparison

/-!
概要：元のGrothendieck–Kan比較を同じ置換単位を固定して前合成同値へ延長する。
方針：元の相対延長のcofinal性を、同じ底上のleft fibrationsの検出へ渡す。
規約：元の底、射影、比較射、置換単位の厳密な等式を保つ。
使われ方：IS-W2 R03fと全分類の比較。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open CategoryTheory SSet
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
variable {I : Type u} [SmallCategory I] (F : I ⥤ Cat.{u,u})

/-- 元の射影と単位を固定した任意の延長は、元の射の前合成同値である。 -/
theorem grothendieckKanCoefficientLift_isPrecompositionEquivalence :
    let P : Over (nerve I) := Over.mk (nerveMap (Grothendieck.forget F))
    let R := (continuousLeftFibrationReplacement (nerve I)).obj P
    ∀ f : R.left ⟶ weightedNerve (grothendieckKanCoefficients F),
      f ≫ weightedNerveProjection (grothendieckKanCoefficients F) = R.hom →
      ((continuousLeftFibrationReplacementUnit (nerve I)).app P).left ≫ f =
        grothendieckKanCoefficientMap F → IsPrecompositionEquivalence f := by
  dsimp only
  intro f hbase hunit
  have : ∀ i, KanComplex ((grothendieckKanCoefficients F).obj i) := fun i => by
    change KanComplex (exInfinity.obj (nerve (F.obj i)))
    infer_instance
  exact isPrecompositionEquivalence_of_leftCofinal_overLeftFibrations _ _ f hbase
    (grothendieckKanCoefficientLift_isLeftCofinal F f hunit)

/-- R03f：同じ元の比較射を、同じ元の置換単位を固定した前合成同値へ延長する。 -/
theorem exists_grothendieckKanCoefficientComparison :
    let P : Over (nerve I) := Over.mk (nerveMap (Grothendieck.forget F))
    let R := (continuousLeftFibrationReplacement (nerve I)).obj P
    ∃ f : R.left ⟶ weightedNerve (grothendieckKanCoefficients F),
      f ≫ weightedNerveProjection (grothendieckKanCoefficients F) = R.hom ∧
      ((continuousLeftFibrationReplacementUnit (nerve I)).app P).left ≫ f =
        grothendieckKanCoefficientMap F ∧ IsPrecompositionEquivalence f := by
  obtain ⟨f, hbase, hunit⟩ := exists_grothendieckKanCoefficientLift F
  exact ⟨f, hbase, hunit,
    grothendieckKanCoefficientLift_isPrecompositionEquivalence F f hbase hunit⟩
end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
