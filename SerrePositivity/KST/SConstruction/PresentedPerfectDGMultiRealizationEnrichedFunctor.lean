module
public import SerrePositivity.KST.SConstruction.SimplicialDiagramDiagonalEnrichedFunctor
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGMultiSCoreObjectFunctor

/-! # 全厳密 dg 入力を持つ元の反復実現
概要：元の反復 core S• の対角実現を、同じ全 native Kan 入力を保つ厳密豊穣関手にする。
方針：図式全体への厳密豊穣関手と、元の対角実現の厳密豊穣関手を合成する。
規約：Kan 置換・BF は後続。使われ方：全パラメータを持つ連結 K の実現段階。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A]

/-- 元の全反復実現への、全 native Kan dg 入力を保持する厳密豊穣関手。 -/
def presentedPerfectDGMultiRealizationEnrichedFunctor (r : ℕ) :
    EnrichedFunctor SSet.{max (u + 1) v} (PerfDGInput.{u, v} A)
      SSetInternalObject.{max (u + 1) v} :=
  (presentedPerfectDGMultiSCoreObjectEnrichedFunctor A r).comp SSet
    simplicialSSetDiagramDiagonalEnrichedFunctor

/-- 実値は同じ元の全反復 core S• の対角実現。 -/
lemma presentedPerfectDGMultiRealizationEnrichedFunctor_obj (r : ℕ)
    (C : PerfDGInput.{u, v} A) :
    ((presentedPerfectDGMultiRealizationEnrichedFunctor A r).obj C).obj =
      multiDiagonalCoreSConstruction r
        (stableCategoryModel (presentedPerfectDGStableCategory A C)) := rfl

/-- 元の通常 dg 射では、同じ元の反復実現の射を全単体で厳密に回収する。 -/
lemma presentedPerfectDGMultiRealizationEnrichedFunctor_hom (r : ℕ)
    {C D : PerfDGInput.{u, v} A} (F : C ⟶ D) :
    eHomEquiv SSet.{max (u + 1) v} F ≫
      (presentedPerfectDGMultiRealizationEnrichedFunctor A r).map C D =
        curry' (C := SSet.{max (u + 1) v}) ((multiRealizationFunctor r).map
          ⟨(presentedPerfectDGExactMap A F).hom,
            preservesCofiberData_of_isExactFunctor (presentedPerfectDGExactMap A F).hom⟩) := by
  change eHomEquiv SSet.{max (u + 1) v} F ≫
    ((presentedPerfectDGMultiSCoreObjectEnrichedFunctor A r).map C D ≫
      simplicialSSetDiagramDiagonalEnrichedFunctor.map _ _) = _
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun f => f ≫ simplicialSSetDiagramDiagonalEnrichedFunctor.map _ _)
      (presentedPerfectDGMultiSCoreObjectEnrichedFunctor_hom A r F)).trans
        (simplicialSSetDiagramDiagonalEnrichedFunctor_hom
          (presentedPerfectDGMultiSCoreObjectMap A r F)))

end SerrePositivity.KST.SConstruction
