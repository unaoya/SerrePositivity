module
public import SerrePositivity.KST.SConstruction.SimplicialDiagramDiagonalEnrichedFunctor
public import SerrePositivity.KST.SConstruction.StableMultiSCoreObjectFunctor

/-! # 全自然同値入力を持つ元の反復実現
概要：元の反復 core S• の対角実現を、同じ全自然同値入力を保つ厳密豊穣関手にする。
方針：図式全体への厳密豊穣関手と、元の対角実現の厳密豊穣関手を合成する。
規約：Kan 置換・BF は後続。使われ方：全パラメータを持つ連結 K の実現段階。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories LocalizingInvariants

/-- 元の全反復実現への、全自然同値入力を保持する厳密豊穣関手。 -/
def stableMultiRealizationEnrichedFunctor (r : ℕ) :
    EnrichedFunctor SSet.{u} _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}
      SSetInternalObject.{u} :=
  (stableMultiSCoreObjectEnrichedFunctor r).comp SSet
    simplicialSSetDiagramDiagonalEnrichedFunctor

/-- 実値は同じ元の全反復 core S• の対角実現。 -/
lemma stableMultiRealizationEnrichedFunctor_obj (r : ℕ)
    (C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) :
    ((stableMultiRealizationEnrichedFunctor r).obj C).obj =
      multiDiagonalCoreSConstruction r
        (stableCategoryModel (C)) := rfl

/-- 元の通常の完全射では、同じ元の反復実現の射を全単体で厳密に回収する。 -/
lemma stableMultiRealizationEnrichedFunctor_hom (r : ℕ)
    {C D : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}} (F : C ⟶ D) :
    eHomEquiv SSet.{u} F ≫
      (stableMultiRealizationEnrichedFunctor r).map C D =
        curry' (C := SSet.{u}) ((multiRealizationFunctor r).map
          ⟨(F).hom,
            @preservesCofiberData_of_isExactFunctor _ _ F.hom F.isExact⟩) := by
  change eHomEquiv SSet.{u} F ≫
    ((stableMultiSCoreObjectEnrichedFunctor r).map C D ≫
      simplicialSSetDiagramDiagonalEnrichedFunctor.map _ _) = _
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun f => f ≫ simplicialSSetDiagramDiagonalEnrichedFunctor.map _ _)
      (stableMultiSCoreObjectEnrichedFunctor_hom r F)).trans
        (simplicialSSetDiagramDiagonalEnrichedFunctor_hom
          (stableMultiSCoreObjectMap r F)))

end SerrePositivity.KST.SConstruction
