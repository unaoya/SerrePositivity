module
public import SerrePositivity.KST.Fibration.RelativeSKernelDiagonalContraction

/-! # 元の零段の零対象から指定する相対 S の核の基点 -/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Fibration

/-- 元の S₀ の零対象を相対全単体の同型で戻し、同じ対角の基点にする。 -/
def relativeSKernelBasepoint
    {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C}
    (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q) : Δ[0] ⟶ simplicialDiagonalFunctor.obj
      (relativeSimplicialSConstruction (i.hom ≫ q.hom)) :=
  yonedaEquiv.symm ((relativeSKernelTopIso h 0).inv.app (Opposite.op ⦋0⦌)
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.chosenZeroVertex (sConstruction 0 A.obj)).vertex)

end SerrePositivity.KST.Fibration
