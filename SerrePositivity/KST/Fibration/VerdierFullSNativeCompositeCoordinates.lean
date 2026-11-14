module
public import SerrePositivity.KST.Fibration.VerdierFullSNativeComparison
public import SerrePositivity.KST.Fibration.QuotientSKernelFullSKanAction

/-!
概要：全 S• 上の native 合成点を、指定 Verdier 両端と元の商核上辺へ戻す。
方針：元の対象等号だけに沿って同じ実射を輸送し、全 S• 上辺の厳密等式を実現する。
規約：元の合成 path・指定した包含と商・全 S• 始域を保持する。
使われ方：指定二胞体の比較端点と元の商核四角形の実上辺との照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction
open SerrePositivity.KST.LocalizingInvariants

namespace SerrePositivity.KST.Fibration

/-- 元の安定対象の等号に沿う移送は、同じ零値完全関手の全 S• native 実射を保つ。 -/
theorem zeroFunctorFullSNativeKanMap_transport_heq {A C A' C' : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (hA : A = A') (hC : C = C') (F : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A C)
    (hF : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F.hom))
    (hF' : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (exactMapTransport hA hC F).hom)) :
    HEq (zeroFunctorFullSNativeKanMap (A := (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from A'))
        (C := (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from C')) (exactMapTransport hA hC F) hF')
      (zeroFunctorFullSNativeKanMap (A := (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from A))
        (C := (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from C)) F hF) := by
  cases hA
  cases hC
  rfl

/-- 元の合成点の全 S• native 実射は、指定両端に戻しても同じ元の実射である。 -/
theorem verdierNullCompositeNativeKanMap_original_heq (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) (j : Fin 2) :
    HEq (zeroFunctorFullSNativeKanMap (A := (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from d.left))
        (C := (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from d.right)) (verdierNullCompositeOriginalMap d j)
          (isZeroVertex_functorVertex_of_pointwise _ (verdierNullCompositeOriginalMap_zero d j)))
      (zeroFunctorFullSNativeKanMap (verdierNullCompositeMap d j)
        (isZeroVertex_functorVertex_of_pointwise _ (verdierNullCompositeMap_zero d j))) :=
  zeroFunctorFullSNativeKanMap_transport_heq (verdierNullDiagonal_source d)
    (verdierNullDiagonal_target d) _ _ _

/-- 元の商核上辺の native 像は、同じ核包含同型後の全 S• 零値実射に厳密一致する。 -/
theorem quotientSKernelTop_fullSNativeKanMap
    {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C}
    (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map (simplicialDiagonalFunctor.map (relativeSKernelSimplicialIso h).hom) ≫
        (show (fullSRealizationKanObject A).obj ⟶
          ((stableMultiKanEnrichedFunctor 0).obj (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from C)).obj from
          zeroFunctorFullSNativeKanMap (A := (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from A))
            (C := (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from C))
            (show A ⟶ C from (show A ⟶ B from i) ≫ (show B ⟶ C from q))
            (verdierSequenceComposite_zero h)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map (simplicialDiagonalFunctor.map
        (relativeSimplicialFunctorMap i q.hom ≫ relativeSimplicialQuotientMap q)) ≫
          (coreSingleKanIso (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from C)).hom := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map _ ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map _ ≫ _) = _
  rw [← Category.assoc, ← Functor.map_comp, ← Functor.map_comp,
    ← quotientSKernelTop_zeroFunctorFullSMap h]

end SerrePositivity.KST.Fibration
