module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGInvertingHomExtension
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGInvertingRoofPostcomposition
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.WeakRoofDescentNaturality

/-! # 任意標的への商 Hom 延長の自然性

概要：反転関手の商 Hom への延長は、任意の標的関手による後合成とホモトピーまで可換。
方針：実屋根の厳密な後合成則を、二つの弱同値による降下の自然性に渡す。
規約：標的は任意の quasicategory。使われ方：局所化の全関手圏比較への組み立て。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D]

/-- 商の実 Hom 全体への延長は、任意標的の後合成に関してホモトピー自然。 -/
theorem dgInvertingHomMap_postcomp (P : Set D) (hP : _root_.SerrePositivity.DifferentialGraded.DGQuotient.localKFlat A D P)
    (x y : D) {Y Z : SSet.{max u v}} [Quasicategory Y] [Quasicategory Z]
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D ⟶ Y) (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges F (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P)) (G : Y ⟶ Z)
    (C : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGInvertingHomDescent A D P x y F) (C' : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGInvertingHomDescent A D P x y (F ≫ G)) :
    Nonempty (SSet.Homotopy
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGInvertingHomDescent.homMap A D P x y F C ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap G
        (F.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x))
        (F.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y)))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGInvertingHomDescent.homMap A D P x y (F ≫ G) C')) := by
  obtain ⟨H⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.weakRoofDescent_naturality
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceMap_isWeakHomotopyEquivalence A D P hP x y)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingFixedHomRoofMap_isWeakHomotopyEquivalence A D P x F hF
      (F.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y)))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingRoofFunctorMap A D P x y F)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingRoofFunctorMap A D P x y (F ≫ G))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingRoofPostcompMap A D P x F G
      (F.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y)))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap G (F.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x))
      (F.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y)))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingFixedHomRoofMap_postcomp A D P x F G _)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingRoofFunctorMap_postcomp A D P x y F G)
    C.evaluation C'.evaluation C.extension C'.extension
    C.evaluation_homotopy C'.evaluation_homotopy C.extension_homotopy C'.extension_homotopy
  simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGInvertingHomDescent.homMap, Category.assoc] using
    (show Nonempty (SSet.Homotopy
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientFixedHomRoofMap A D P x y ≫ (C.extension ≫ _))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientFixedHomRoofMap A D P x y ≫ C'.extension)) from
        ⟨_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp H (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientFixedHomRoofMap A D P x y)⟩)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
