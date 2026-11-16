module

public import SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotJointNativeUnitFiber

/-!
概要：同じ全空間の射の元の単位条件から、同じnative fiberの単位の値を回収する。
方針：元のfiber単位の合成則を同じpullback同型で後合成し、同じ単位点で評価する。
規約：元の射・底の等式・元の単位条件を保持し、弱同値を追加で仮定しない。
使われ方：元の全straightening比較の単位評価の照合への接続。
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory HomotopicalAlgebra SSet
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport
open scoped Simplicial
open SerrePositivity.EInfinity.BarrattEccles
open SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
open SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans

noncomputable section

namespace SerrePositivity.EInfinity.BarrattEccles

variable (A : Type u) [CommRing A]
local instance jointNativeLiftUnitModel : ModelCategory (operad A).Algebra := modelCategory A
local instance jointNativeLiftUnitFactorization :
    (cofibrations (operad A).Algebra).HasFunctorialFactorization
      (trivialFibrations (operad A).Algebra) := ⟨⟨mappingCofibrantFactorization A⟩⟩
/-- 元の単位条件を満たす同じ全空間の射は、同じ単位とpullback同型の合成で元のnative fiber射を回収する。 -/
lemma strictBETotJointSourceNativeLiftUnit_twistedFiberMap
    (m : (simplicialElementsReplacement (strictBETotJointSourceCoefficients A)).left ⟶
      strictBETotJointNativeHomTotalSpace A)
    (hm : m ≫ strictBETotJointNativeHomProjection A =
      (simplicialElementsReplacement (strictBETotJointSourceCoefficients A)).hom)
    (hu : ((continuousLeftFibrationReplacementUnit (nerve (strictBETotJointHomIndex A))).app
      (Over.mk (nerveMap (strictBETotJointSourceElementsProjection A)))).left ≫ m =
        strictBETotJointSourceNativeHomMap A) (P : strictBETotJointHomIndex A) :
    simplicialElementsFiberUnit (strictBETotJointSourceCoefficients A) P ≫
      vertexFiberMap (simplicialElementsReplacement (strictBETotJointSourceCoefficients A)).hom
        (strictBETotJointNativeHomProjection A) m hm (nerveVertex P) ≫
        (vertexFiberPullbackIso (twistedArrowProjection (CAlg_R A))
          (strictBETotJointNativeHomInput A) (nerveVertex P)).hom =
            strictBETotJointSourceNativeTwistedFiberMap A P := by
  have h₀ := strictBETotJointSourceNativeFiberUnit_map A m hm hu P
  have h := congrArg (fun f :
      nerve ((simplicialElementsCatDiagram (strictBETotJointSourceCoefficients A)).obj P) ⟶
        vertexFiber (strictBETotJointNativeHomProjection A) (nerveVertex P) => f ≫
    (vertexFiberPullbackIso (twistedArrowProjection (CAlg_R A))
      (strictBETotJointNativeHomInput A) (nerveVertex P)).hom)
    h₀
  have h₁ := Category.assoc
    (simplicialElementsFiberUnit (strictBETotJointSourceCoefficients A) P)
    (vertexFiberMap (simplicialElementsReplacement (strictBETotJointSourceCoefficients A)).hom
        (strictBETotJointNativeHomProjection A) m hm (nerveVertex P))
    (vertexFiberPullbackIso (twistedArrowProjection (CAlg_R A))
      (strictBETotJointNativeHomInput A) (nerveVertex P)).hom
  exact h₁.symm.trans h
/-- 元の単位条件を満たす同じ全空間の射の元の単位点の像は、元のnative恒等射の辺の類になる。 -/
lemma strictBETotJointSourceNativeLiftUnit_unit_arrow
    (m : (simplicialElementsReplacement (strictBETotJointSourceCoefficients A)).left ⟶
      strictBETotJointNativeHomTotalSpace A)
    (hm : m ≫ strictBETotJointNativeHomProjection A =
      (simplicialElementsReplacement (strictBETotJointSourceCoefficients A)).hom)
    (hu : ((continuousLeftFibrationReplacementUnit (nerve (strictBETotJointHomIndex A))).app
      (Over.mk (nerveMap (strictBETotJointSourceElementsProjection A)))).left ≫ m =
        strictBETotJointSourceNativeHomMap A) (X : (operad A).Algebra) :
    Arrow.mk (HomotopyCategory.homMk (twistedArrowVertexEdge
      (((simplicialElementsFiberUnit (strictBETotJointSourceCoefficients A)
          (strictBETotJointUnitIndex A X) ≫
        vertexFiberMap (simplicialElementsReplacement (strictBETotJointSourceCoefficients A)).hom
          (strictBETotJointNativeHomProjection A) m hm (nerveVertex (strictBETotJointUnitIndex A X)) ≫
        (vertexFiberPullbackIso (twistedArrowProjection (CAlg_R A))
          (strictBETotJointNativeHomInput A) (nerveVertex (strictBETotJointUnitIndex A X))).hom).app
          (Opposite.op ⦋0⦌) (nerveVertex (strictBETotJointSourceNativeUnitFiberElement A X))).val))) =
      Arrow.mk (𝟙 (HomotopyCategory.mk ((strictBETotModelSource A).app
        (Opposite.op ⦋0⦌) (nerveVertex (modelRelativeObject (operad A).Algebra X))))) := by
  have h := congrArg (fun f => Arrow.mk (HomotopyCategory.homMk (twistedArrowVertexEdge
    ((f.app (Opposite.op ⦋0⦌)
      (nerveVertex (strictBETotJointSourceNativeUnitFiberElement A X))).val))))
    (strictBETotJointSourceNativeLiftUnit_twistedFiberMap A m hm hu (strictBETotJointUnitIndex A X))
  exact h.trans (strictBETotJointSourceNativeTwistedFiberMap_unit_arrow A X)

end SerrePositivity.EInfinity.BarrattEccles

end
