module
public import SerrePositivity.InfinityCategories.Derived.DGInvertingHomExtension
public import SerrePositivity.InfinityCategories.Derived.DGInvertingRoofPostcomposition
public import SerrePositivity.InfinityCategories.Derived.WeakRoofDescentNaturality

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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable [IsDGPretriangulated A D]

/-- 商の実 Hom 全体への延長は、任意標的の後合成に関してホモトピー自然。 -/
theorem dgInvertingHomMap_postcomp (P : Set D) (hP : DGQuotient.localKFlat A D P)
    (x y : D) {Y Z : SSet.{max u v}} [Quasicategory Y] [Quasicategory Z]
    (F : dgNerve A D ⟶ Y) (hF : InvertsEdges F (dgVerdierEdges A D P)) (G : Y ⟶ Z)
    (C : DGInvertingHomDescent A D P x y F) (C' : DGInvertingHomDescent A D P x y (F ≫ G)) :
    Nonempty (SSet.Homotopy
      (DGInvertingHomDescent.homMap A D P x y F C ≫ pinchedHomMap G
        (F.app (Opposite.op ⦋0⦌) (Simplex.vertex x))
        (F.app (Opposite.op ⦋0⦌) (Simplex.vertex y)))
      (DGInvertingHomDescent.homMap A D P x y (F ≫ G) C')) := by
  obtain ⟨H⟩ := weakRoofDescent_naturality
    (dgRoofCorrespondenceMap_isWeakHomotopyEquivalence A D P hP x y)
    (dgInvertingFixedHomRoofMap_isWeakHomotopyEquivalence A D P x F hF
      (F.app (Opposite.op ⦋0⦌) (Simplex.vertex y)))
    (dgInvertingRoofFunctorMap A D P x y F)
    (dgInvertingRoofFunctorMap A D P x y (F ≫ G))
    (dgInvertingRoofPostcompMap A D P x F G
      (F.app (Opposite.op ⦋0⦌) (Simplex.vertex y)))
    (pinchedHomMap G (F.app (Opposite.op ⦋0⦌) (Simplex.vertex x))
      (F.app (Opposite.op ⦋0⦌) (Simplex.vertex y)))
    (dgInvertingFixedHomRoofMap_postcomp A D P x F G _)
    (dgInvertingRoofFunctorMap_postcomp A D P x y F G)
    C.evaluation C'.evaluation C.extension C'.extension
    C.evaluation_homotopy C'.evaluation_homotopy C.extension_homotopy C'.extension_homotopy
  simpa only [DGInvertingHomDescent.homMap, Category.assoc] using
    (show Nonempty (SSet.Homotopy
      (dgQuotientFixedHomRoofMap A D P x y ≫ (C.extension ≫ _))
      (dgQuotientFixedHomRoofMap A D P x y ≫ C'.extension)) from
        ⟨functorHomotopyPrecomp H (dgQuotientFixedHomRoofMap A D P x y)⟩)

end SerrePositivity.InfinityCategories
