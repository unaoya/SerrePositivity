module
public import SerrePositivity.KST.Fibration.ZeroMiddleFullSKanTriangle
public import SerrePositivity.KST.Fibration.ZeroFunctorFullSNativeKanVertices

/-!
概要：元の零中間二胞体の全 S• 延長が、同じ二短辺の厳密合成を端点に持つことを示す。
方針：元の合成 path を同じ完全射へ回収し、全 S• 作用の合成則と固定関手評価を使う。
規約：元の次数を含む全長 Hom を保ち、合成端を新しく選ばない。
使われ方：coherent 中間対象輸送の長 Hom と短辺合成の整合条件。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction
open SerrePositivity.KST.LocalizingInvariants

namespace SerrePositivity.KST.Fibration

/-- 同じ指定完全関手の実点は、全 S• Kan 族でも同じ元の実現射を表す。 -/
theorem zeroFunctorFullSKanFamily_vertex {A C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}} (F : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A C)
    (hF : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F.hom)) :
    (zeroFunctorFullSKanFamily A C).app (Opposite.op ⦋0⦌)
        (fullSubcategoryVertex _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F.hom) hF) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map (simplicialDiagonalFunctor.map (zeroFunctorFullSMap F hF))) := by
  have h := congrArg (SSet.unitHomEquiv _) (zeroFunctorFullSKanFamily_fixed F hF)
  exact h

variable (s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u} _⦋2⦌) (hZ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.IsZeroCategory (s.obj ⟨ULift.up 1⟩))
include hZ in
/-- 元の二胞体の合成 path は、同じ実零値完全関手を表す。 -/
theorem zeroMiddleTriangle_composite_zero :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (stableTriangleCompositeMap s).hom) :=
  stableHomZeroVertex_functorVertex _ (stableTriangleFullPath_zero s hZ)

/-- 元の合成 path の完全射による、同じ全 S• の実 Kan 射。 -/
def zeroMiddleFullSKanComposite :
    fullSRealizationKanObject (s.obj ⟨ULift.up 0⟩) ⟶
      stableCoreSingleKanObject (s.obj ⟨ULift.up 2⟩) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map (simplicialDiagonalFunctor.map
    (zeroFunctorFullSMap (stableTriangleCompositeMap s) (zeroMiddleTriangle_composite_zero s hZ)))

/-- 同じ中間対象比較と元の第二短辺の合成は、元の合成 path の実射に厳密一致する。 -/
theorem zeroMiddleFullSKanComparison_last :
    zeroMiddleFullSKanComparison s hZ ≫
        stableCoreSingleKanMap (stableArrowExactMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.δ 0 s)) =
      zeroMiddleFullSKanComposite s hZ := by
  have hFG := zeroMiddleTriangle_composite_zero s hZ
  rw [stableTriangleCompositeMap_eq_comp s] at hFG
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map _ = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map _
  rw [← Functor.map_comp, ← Functor.map_comp]
  apply congrArg (fun f => _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map (simplicialDiagonalFunctor.map f))
  have hc : ∀ (F G : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (s.obj ⟨ULift.up 0⟩) (s.obj ⟨ULift.up 2⟩)) (h : F = G)
      (hf : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F.hom)) (hg : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G.hom)),
      zeroFunctorFullSMap F hf = zeroFunctorFullSMap G hg := by
    intro F G h hf hg
    subst G
    rfl
  exact (zeroFunctorFullSMap_comp _ _ (zeroMiddleTriangle_first_zero s hZ) hFG).trans
    (hc _ _ (stableTriangleCompositeMap_eq_comp s).symm _ _)

set_option maxHeartbeats 800000 in
-- 元の coherent 対象座標と全 S• 実現の頂点表示を同時に照合する。
/-- 全長 Hom 延長の合成 path の値は、元の中間比較と第二短辺の同じ厳密合成。 -/
theorem zeroMiddleFullSKanLongHom_composite :
    (zeroMiddleFullSKanLongHom s hZ).app (Opposite.op ⦋0⦌)
        (ComposableArrows.mk₀ coherentTriangleFullPath) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (show (fullSRealizationKanObject (s.obj ⟨ULift.up 0⟩)).obj ⟶
        (stableCoreSingleKanObject (s.obj ⟨ULift.up 2⟩)).obj from
          zeroMiddleFullSKanComparison s hZ ≫
            stableCoreSingleKanMap (stableArrowExactMap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.δ 0 s))) := by
  have he : (stableTriangleZeroHomLift s hZ).app (Opposite.op ⦋0⦌)
      (ComposableArrows.mk₀ coherentTriangleFullPath) =
        fullSubcategoryVertex _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (stableTriangleCompositeMap s).hom)
          (zeroMiddleTriangle_composite_zero s hZ) := by
    apply Subtype.ext
    exact stableHomAmbient_vertex _
  change (zeroFunctorFullSKanFamily (s.obj ⟨ULift.up 0⟩) (s.obj ⟨ULift.up 2⟩)).app
    (Opposite.op ⦋0⦌) ((stableTriangleZeroHomLift s hZ).app (Opposite.op ⦋0⦌)
      (ComposableArrows.mk₀ coherentTriangleFullPath)) = _
  rw [he]
  exact (zeroFunctorFullSKanFamily_vertex _ _).trans
    (congrArg (fun f : fullSRealizationKanObject (s.obj ⟨ULift.up 0⟩) ⟶
        stableCoreSingleKanObject (s.obj ⟨ULift.up 2⟩) =>
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (show (fullSRealizationKanObject (s.obj ⟨ULift.up 0⟩)).obj ⟶
        (stableCoreSingleKanObject (s.obj ⟨ULift.up 2⟩)).obj from f))
      (zeroMiddleFullSKanComparison_last s hZ).symm)

end SerrePositivity.KST.Fibration
