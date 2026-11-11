module
public import SerrePositivity.KST.Fibration.ZeroFunctorFullSNativeKanVertices
public import SerrePositivity.KST.Fibration.ZeroFunctorFullSRelativeComparison

/-!
概要：元の Verdier 上下二胞体の長 Hom を、全 S• 始域を持つ同じ native 族へ延長する。
方針：同じ零値全族を全 S• に作用させ、実 core 包含で元の native 長 Hom を回収する。
規約：共有対角・元の合成 path・元の全二胞体を保持し、対象座標だけを輸送する。
使われ方：指定二胞体を保つ全四角形比較の三角柱入力。
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

/-- 同じ native 正反復実現は、対象座標の輸送後も元の全長 Hom を保持する。 -/
theorem stableTriangleHomOverDiagonal_native_heq (a : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u} _⦋1⦌)
    (s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u} _⦋2⦌) (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.δ 1 s = a) :
    HEq (stableTriangleHomOverDiagonal a s h ≫
        (stableMultiKanEnrichedFunctor 0).map (a.obj ⟨ULift.up 0⟩) (a.obj ⟨ULift.up 1⟩))
      (coherentTriangleLongHom ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (stableMultiKanEnrichedFunctor 0)).app
        (Opposite.op ⦋2⦌) s)) := by
  subst a
  rfl

/-- 元の上下二胞体の同じ全長 Hom を、全 S• 始域の native 関手族へ延長する。 -/
def verdierNullHomFullSNativeFamily (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) (j : Fin 2) :
    nerve (CategoryTheory.SimplicialThickening.Path
      (ULift.up (0 : Fin 3) : ULift.{u} (Fin 3)) (ULift.up 2)) ⟶
        (ihom (fullSRealizationKanObject ((verdierNullDiagonal d).obj ⟨ULift.up 0⟩)).obj).obj
          ((stableMultiKanEnrichedFunctor 0).obj ((verdierNullDiagonal d).obj ⟨ULift.up 1⟩)).obj :=
  zeroStableHomFamilyLift (verdierNullHomFamily d j) (verdierNullHomFamily_zero d j) ≫
    zeroFunctorFullSNativeKanFamily ((verdierNullDiagonal d).obj ⟨ULift.up 0⟩)
      ((verdierNullDiagonal d).obj ⟨ULift.up 1⟩)

/-- 元の実 core 包含で制限すると、同じ元の全 native Hom 作用を厳密に回収する。 -/
theorem verdierNullHomFullSNativeFamily_core (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) (j : Fin 2) :
    verdierNullHomFullSNativeFamily d j ≫
        (pre (C := SSet.{u}) (fullSNativeCoreInclusion
          ((verdierNullDiagonal d).obj ⟨ULift.up 0⟩))).app
            ((stableMultiKanEnrichedFunctor 0).obj ((verdierNullDiagonal d).obj ⟨ULift.up 1⟩)).obj =
      verdierNullHomFamily d j ≫ (stableMultiKanEnrichedFunctor 0).map
        ((verdierNullDiagonal d).obj ⟨ULift.up 0⟩) ((verdierNullDiagonal d).obj ⟨ULift.up 1⟩) := by
  rw [verdierNullHomFullSNativeFamily, Category.assoc, zeroFunctorFullSNativeKanFamily_core,
    ← Category.assoc, zeroStableHomFamilyLift_recovery]

/-- 同じ core 制限は、元の指定二胞体の native 像の全長 Hom そのものである。 -/
theorem verdierNullHomFullSNativeFamily_original_heq (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) (j : Fin 2) :
    HEq (verdierNullHomFullSNativeFamily d j ≫
        (pre (C := SSet.{u}) (fullSNativeCoreInclusion
          ((verdierNullDiagonal d).obj ⟨ULift.up 0⟩))).app
            ((stableMultiKanEnrichedFunctor 0).obj ((verdierNullDiagonal d).obj ⟨ULift.up 1⟩)).obj)
      (coherentTriangleLongHom ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (stableMultiKanEnrichedFunctor 0)).app
        (Opposite.op ⦋2⦌) (verdierTriangle d j))) :=
  (heq_of_eq (verdierNullHomFullSNativeFamily_core d j)).trans
    (stableTriangleHomOverDiagonal_native_heq _ _ (verdierTriangle_diagonal d j))

/-- 全 S• 上への延長後も、上下二胞体の直接 path は同じ共有対角に厳密一致する。 -/
theorem verdierNullHomFullSNativeFamily_same_direct (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) (j k : Fin 2) :
    coherentTriangleDirectVertexMap ≫ verdierNullHomFullSNativeFamily d j =
      coherentTriangleDirectVertexMap ≫ verdierNullHomFullSNativeFamily d k := by
  simp only [verdierNullHomFullSNativeFamily, ← Category.assoc]
  exact congrArg (· ≫ zeroFunctorFullSNativeKanFamily
    ((verdierNullDiagonal d).obj ⟨ULift.up 0⟩) ((verdierNullDiagonal d).obj ⟨ULift.up 1⟩))
    (zeroStableHomFamilyLift_restriction _ _ _ (verdierNullHomFamily_zero d j)
      (verdierNullHomFamily_zero d k) (verdierNullHomFamily_same_direct d j k))

/-- 同じ元の合成 path の実点は、元の合成完全射の同じ全 S• 実射を表す。 -/
theorem verdierNullHomFullSNativeFamily_composite (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) (j : Fin 2) :
    (verdierNullHomFullSNativeFamily d j).app (Opposite.op ⦋0⦌)
        (ComposableArrows.mk₀ coherentTriangleFullPath) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (show (fullSRealizationKanObject
          ((verdierNullDiagonal d).obj ⟨ULift.up 0⟩)).obj ⟶
        ((stableMultiKanEnrichedFunctor 0).obj ((verdierNullDiagonal d).obj ⟨ULift.up 1⟩)).obj from
          zeroFunctorFullSNativeKanMap (verdierNullCompositeMap d j)
            (isZeroVertex_functorVertex_of_pointwise _ (verdierNullCompositeMap_zero d j))) :=
  zeroStableHomFamilyLift_fullSNativeKan_vertex _ (verdierNullHomFamily_zero d j) _

end SerrePositivity.KST.Fibration
