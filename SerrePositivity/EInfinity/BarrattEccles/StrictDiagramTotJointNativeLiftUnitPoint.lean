module

public import SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotJointNativeLiftUnit
public import SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotJointNativeUnitPoint

/-!
概要：元の置換単位を保つ同じ全空間の射の実fiberで、単位点の像を照合する。
方針：元の全写像の単位条件と同じfiber単位の厳密な式を、R03iの同じ単位点の比較へ合成する。
規約：元の単位条件だけを使い、射の弱同値性は仮定しない。
使われ方：元のnative全変換の指定単位の評価。
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet HomotopicalAlgebra
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
open scoped Simplicial
open SerrePositivity.EInfinity.BarrattEccles
open SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes

noncomputable section

namespace SerrePositivity.EInfinity.BarrattEccles

variable (A : Type u) [CommRing A]
local instance jointNativeLiftUnitPointModel : ModelCategory (operad A).Algebra := modelCategory A
local instance jointNativeLiftUnitPointFactorization :
    (cofibrations (operad A).Algebra).HasFunctorialFactorization
      (trivialFibrations (operad A).Algebra) := ⟨⟨mappingCofibrantFactorization A⟩⟩

/-- 元の置換単位を保つ同じ全空間の射は、同じ実fiberの単位点を元の恒等点と同型な点へ送る。 -/
lemma strictBETotJointSourceNativeLiftUnit_identityPoint
    (m : (simplicialElementsReplacement (strictBETotJointSourceCoefficients A)).left ⟶
      strictBETotJointNativeHomTotalSpace A)
    (hm : m ≫ strictBETotJointNativeHomProjection A =
      (simplicialElementsReplacement (strictBETotJointSourceCoefficients A)).hom)
    (hu : ((continuousLeftFibrationReplacementUnit (nerve (strictBETotJointHomIndex A))).app
      (Over.mk (nerveMap (strictBETotJointSourceElementsProjection A)))).left ≫ m =
        strictBETotJointSourceNativeHomMap A) (X : (operad A).Algebra) :
    let P := strictBETotJointUnitIndex A X
    Nonempty (VertexIso
      ((strictBETotJointNativeUnitFiberIso A X).hom.app (Opposite.op ⦋0⦌)
        (((simplicialElementsFiberUnit (strictBETotJointSourceCoefficients A) P ≫
          vertexFiberMap (simplicialElementsReplacement (strictBETotJointSourceCoefficients A)).hom
            (strictBETotJointNativeHomProjection A) m hm (nerveVertex P) ≫
          (vertexFiberPullbackIso (twistedArrowProjection (CAlg_R A))
            (strictBETotJointNativeHomInput A) (nerveVertex P)).hom).app (Opposite.op ⦋0⦌)
              (nerveVertex (strictBETotJointSourceNativeUnitFiberElement A X)))))
      (twistedArrowHomSpaceIdentityPoint ((strictBETotModelSource A).app (Opposite.op ⦋0⦌)
        (nerveVertex (modelRelativeObject (operad A).Algebra X))))) := by
  dsimp only
  have h := congrArg (fun f :
      nerve ((simplicialElementsCatDiagram (strictBETotJointSourceCoefficients A)).obj
        (strictBETotJointUnitIndex A X)) ⟶
          vertexFiber (twistedArrowProjection (CAlg_R A))
            ((strictBETotJointNativeHomInput A).app (Opposite.op ⦋0⦌)
              (nerveVertex (strictBETotJointUnitIndex A X))) =>
    (strictBETotJointNativeUnitFiberIso A X).hom.app (Opposite.op ⦋0⦌)
      (f.app (Opposite.op ⦋0⦌) (nerveVertex (strictBETotJointSourceNativeUnitFiberElement A X))))
    (strictBETotJointSourceNativeLiftUnit_twistedFiberMap A m hm hu (strictBETotJointUnitIndex A X))
  change _ = strictBETotJointNativeUnitPoint A X at h
  rw [h]
  exact strictBETotJointNativeUnitPoint_identityIso A X

end SerrePositivity.EInfinity.BarrattEccles

end
