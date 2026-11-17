module
public import SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.StrictDiagramTotJointSourceNativeFiberPairing
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.OppositeWeakHomotopyReflection
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.NerveOpposite

/-!
状態：D81により停止したBE模型のIS-W2 Tot経路。既存の到達点の保管用。
概要：元のnative fiber射そのものを、同じ反対要素圏の始域へ移す。
方針：同じop反転と元のnerve反転同型を合成し、弱同値性を厳密に反映する。
規約：元の制限写像と弱同値のfiber単位を記録し、native比較の同値性はまだ主張しない。
使われ方：同じfiber制限を元の固定始域のroof比較へ照合する。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot
open _root_.CategoryTheory _root_.HomotopicalAlgebra _root_.SSet _root_.CategoryTheory.Limits
open _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
open _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
open _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
open _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
open scoped _root_.Simplicial
open _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories
open _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
variable (A : Type u) [CommRing A]
local instance jointNativeOppositeFiberModel : ModelCategory (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra := _root_.SerrePositivity.EInfinity.BarrattEccles.modelCategory A
local instance jointNativeOppositeFiberFactorization :
    (cofibrations (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra).HasFunctorialFactorization
      (trivialFibrations (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) := ⟨⟨_root_.SerrePositivity.EInfinity.BarrattEccles.mappingCofibrantFactorization A⟩⟩



/-- 元の同じnative fiber射を反転し、元の反対要素圏を始域にする。 -/
def strictBETotJointSourceNativeOppositeFiberMap (P : _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointHomIndex A) :
    nerve ((simplicialElementsCatDiagram (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceCoefficients A)).obj P)ᵒᵖ ⟶
      (vertexFiber (twistedArrowProjection (_root_.SerrePositivity.EInfinity.BarrattEccles.CAlg_R A))
        ((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointNativeHomInput A).app (Opposite.op ⦋0⦌) (nerveVertex P))).op :=
  (nerveOppositeIso
    (C := (simplicialElementsCatDiagram (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceCoefficients A)).obj P)).inv ≫
      SSet.opFunctor.map (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceNativeTwistedFiberMap A P)

/-- 元の同じnerve反転を戻すと、元のnative射のop反転そのものを回収する。 -/
theorem strictBETotJointSourceNativeOppositeFiberMap_recover (P : _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointHomIndex A) :
    (nerveOppositeIso
      (C := (simplicialElementsCatDiagram (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceCoefficients A)).obj P)).hom ≫
        _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceNativeOppositeFiberMap A P =
      SSet.opFunctor.map (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceNativeTwistedFiberMap A P) := by
  rw [_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceNativeOppositeFiberMap, ← Category.assoc,
    Iso.hom_inv_id, Category.id_comp]

/-- 反対要素圏での同じ実射の弱同値性は、元の同じtwisted fiber射の弱同値性に等しい。 -/
theorem strictBETotJointSourceNativeOppositeFiberMap_weak_iff (P : _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointHomIndex A) :
    IsWeakHomotopyEquivalence (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceNativeOppositeFiberMap A P) ↔
      IsWeakHomotopyEquivalence (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceNativeTwistedFiberMap A P) := by
  let e := nerveOppositeIso
    (C := (simplicialElementsCatDiagram (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceCoefficients A)).obj P)
  have he : IsWeakHomotopyEquivalence e.inv :=
    (isPrecompositionEquivalence_of_iso e.symm).isWeakHomotopyEquivalence
  constructor
  · intro hf
    exact (opposite_map_isWeakHomotopyEquivalence_iff _).mp (he.cancel_left hf)
  · intro hf
    exact he.comp ((opposite_map_isWeakHomotopyEquivalence_iff _).mpr hf)

/-- 同じ反対表示での弱同値性は、元のpullbackのnative fiber射自身の弱同値性に等しい。 -/
theorem strictBETotJointSourceNativeOppositeFiberMap_weak_iff_original
    (P : _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointHomIndex A) :
    IsWeakHomotopyEquivalence (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceNativeOppositeFiberMap A P) ↔
      IsWeakHomotopyEquivalence (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceNativeFiberMap A P) := by
  rw [_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceNativeOppositeFiberMap_weak_iff]
  have he := (isPrecompositionEquivalence_of_iso
    (vertexFiberPullbackIso (twistedArrowProjection (_root_.SerrePositivity.EInfinity.BarrattEccles.CAlg_R A))
      (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointNativeHomInput A) (nerveVertex P))).isWeakHomotopyEquivalence
  constructor
  · intro hf
    exact he.cancel_right hf
  · intro hf
    exact hf.comp he
end SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot
