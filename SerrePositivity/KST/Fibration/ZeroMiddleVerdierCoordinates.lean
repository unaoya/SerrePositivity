module
public import SerrePositivity.KST.Fibration.ZeroMiddleFullSKanComposite

/-!
概要：零中間二胞体の全 S• 比較を、元の指定 Verdier 上側二胞体と同じ実射へ戻す。
方針：元の対象座標と指定短辺・合成 path の異種等号で全 Kan 射を照合する。
規約：元の上側二胞体・長 Hom・指定左辺を保持する。
使われ方：coherent 中間対象輸送の実入力を、元の Verdier 四角形へ接続する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction
open SerrePositivity.KST.LocalizingInvariants

namespace SerrePositivity.KST.Fibration

private lemma zeroFullSKanMap_heq {A C A' C' : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (hA : A = A') (hC : C = C') {F : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A C} {G : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A' C'} (hFG : HEq F G)
    (hF : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F.hom)) (hG : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G.hom)) :
    HEq (show fullSRealizationKanObject A ⟶ stableCoreSingleKanObject (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from C) from
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map (simplicialDiagonalFunctor.map (zeroFunctorFullSMap F hF)))
      (show fullSRealizationKanObject A' ⟶ stableCoreSingleKanObject (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from C') from
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map (simplicialDiagonalFunctor.map (zeroFunctorFullSMap G hG))) := by
  cases hA
  cases hC
  cases eq_of_heq hFG
  rfl

/-- 元の上側二胞体から構成した中間比較は、元の指定左辺の同じ全 S• 零角比較である。 -/
theorem zeroMiddleFullSKanComparison_verdier_original_heq (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) :
    HEq (zeroMiddleFullSKanComparison (verdierUpperTriangle d)
        (verdierUpperTriangle_middle_isZero d))
      (verdierFullSZeroCornerKanMap d) := by
  have hf := (stableArrowExactMap_heq (verdierUpperTriangle_first_arrow d)).trans
    (verdierLeftExactMap_original_heq d).symm
  exact zeroFullSKanMap_heq
    ((verdierUpperTriangle_source d).trans (congrArg _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableObject d.left_eq))
    (verdierUpperTriangle_middle d) hf _ _

/-- 元の上側二胞体の合成端も、元の指定両端で読んだ同じ全 S• 合成実射である。 -/
theorem zeroMiddleFullSKanComposite_verdier_original_heq (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) :
    HEq (zeroMiddleFullSKanComposite (verdierUpperTriangle d)
        (verdierUpperTriangle_middle_isZero d))
      (show fullSRealizationKanObject d.left ⟶
        stableCoreSingleKanObject (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from d.right) from
          _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map (simplicialDiagonalFunctor.map
            (zeroFunctorFullSMap (verdierNullCompositeOriginalMap d 0) (verdierUpperComposite_zero d)))) := by
  have hf : HEq (verdierNullCompositeOriginalMap d 0)
      (stableTriangleCompositeMap (verdierUpperTriangle d)) :=
    (exactMapTransport_heq _ _ _).trans
      (stableTriangleHomOverDiagonal_composite_heq _ _ (verdierTriangle_diagonal d 0))
  exact zeroFullSKanMap_heq
    ((verdierUpperTriangle_source d).trans (congrArg _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableObject d.left_eq))
    ((verdierUpperTriangle_target d).trans (congrArg _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableObject d.right_eq)) hf.symm _ _

/-- 全 S• 延長の同じ core 制限は、元の指定 Verdier 上側二胞体の native 長 Hom そのもの。 -/
theorem zeroMiddleFullSKanLongHom_verdier_native_heq (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) :
    HEq (zeroMiddleFullSKanLongHom (verdierUpperTriangle d)
        (verdierUpperTriangle_middle_isZero d) ≫
        (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map (coreSFullRealizationInclusion
          ((verdierUpperTriangle d).obj ⟨ULift.up 0⟩)))).app
          (stableCoreSingleKanObject ((verdierUpperTriangle d).obj ⟨ULift.up 2⟩)).obj)
      (coherentTriangleLongHom ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (stableMultiKanEnrichedFunctor 0)).app
        (Opposite.op ⦋2⦌) (verdierUpperTriangle d))) := by
  have he := congrArg (fun f => f.app (Opposite.op ⦋2⦌) (verdierUpperTriangle d))
    stableCoreSingleKanInfinity_eq
  have hh : ∀ (a b : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋2⦌), a = b →
      HEq (coherentTriangleLongHom a) (coherentTriangleLongHom b) := by
    intro a b h
    cases h
    rfl
  exact (heq_of_eq (zeroMiddleFullSKanLongHom_core _ _)).trans (hh _ _ he)

end SerrePositivity.KST.Fibration
