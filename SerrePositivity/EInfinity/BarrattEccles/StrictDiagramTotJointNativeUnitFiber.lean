module

public import SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotJointCorrectedUnitArrow
public import SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotJointSourceNativeFiberPairing

/-!
概要：同じnative fiber射の元の単位点の辺の類を回収する。
方針：元のfiber包含の厳密な等式を同じ単位の頂点で評価する。
規約：元の係数・単位ラベル・pullback同型・補正済pairingを保持する。
使われ方：全native比較の元の単位の評価の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory HomotopicalAlgebra SSet
open scoped Simplicial
open SerrePositivity.EInfinity.BarrattEccles
open SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans

noncomputable section

namespace SerrePositivity.EInfinity.BarrattEccles

variable (A : Type u) [CommRing A]
local instance jointNativeUnitFiberModel : ModelCategory (operad A).Algebra := modelCategory A
local instance jointNativeUnitFiberFactorization :
    (cofibrations (operad A).Algebra).HasFunctorialFactorization
      (trivialFibrations (operad A).Algebra) := ⟨⟨mappingCofibrantFactorization A⟩⟩

/-- 元の単位ラベルを、同じ係数の全要素の同じfiber内の対象として取る。 -/
def strictBETotJointSourceNativeUnitFiberElement (X : (operad A).Algebra) :
    (simplicialElementsCatDiagram (strictBETotJointSourceCoefficients A)).obj
      (strictBETotJointUnitIndex A X) :=
  { obj := Opposite.op ⦋0⦌
    val := (strictBETotJointSourceUnitLabel A X).val }

/-- 同じfiberの対象を元の全要素へ戻すと、元の単位ラベルそのもの。 -/
lemma strictBETotJointSourceNativeUnitFiberElement_value (X : (operad A).Algebra) :
    (simplicialElementsFiberFunctor (strictBETotJointSourceCoefficients A)
      (strictBETotJointUnitIndex A X)).obj (strictBETotJointSourceNativeUnitFiberElement A X) =
        strictBETotJointSourceUnitLabel A X := rfl

/-- 同じnative fiber射の単位の値は、元の補正済pairingの同じ単位の値。 -/
lemma strictBETotJointSourceNativeTwistedFiberMap_unit_value (X : (operad A).Algebra) :
    ((strictBETotJointSourceNativeTwistedFiberMap A (strictBETotJointUnitIndex A X)).app
      (Opposite.op ⦋0⦌) (nerveVertex (strictBETotJointSourceNativeUnitFiberElement A X))).val =
      (strictBETotJointSourceCorrectedPairing A).app (Opposite.op ⦋0⦌)
        (nerveVertex (strictBETotJointSourceUnitLabel A X)) := by
  have h := congrArg (fun f => f.app (Opposite.op ⦋0⦌)
      (nerveVertex (strictBETotJointSourceNativeUnitFiberElement A X)))
    (strictBETotJointSourceNativeTwistedFiberMap_ι A (strictBETotJointUnitIndex A X))
  rw [simplicialElementsFiberInclusion_eq_nerveMap] at h
  have hv : (nerveMap (simplicialElementsFiberFunctor (strictBETotJointSourceCoefficients A)
      (strictBETotJointUnitIndex A X))).app (Opposite.op ⦋0⦌)
      (nerveVertex (strictBETotJointSourceNativeUnitFiberElement A X)) =
        nerveVertex (strictBETotJointSourceUnitLabel A X) :=
    ComposableArrows.ext₀ rfl
  change ((strictBETotJointSourceNativeTwistedFiberMap A (strictBETotJointUnitIndex A X)).app
    (Opposite.op ⦋0⦌) (nerveVertex (strictBETotJointSourceNativeUnitFiberElement A X))).val =
    (strictBETotJointSourceCorrectedPairing A).app (Opposite.op ⦋0⦌)
      ((nerveMap (simplicialElementsFiberFunctor (strictBETotJointSourceCoefficients A)
        (strictBETotJointUnitIndex A X))).app _ (nerveVertex (strictBETotJointSourceNativeUnitFiberElement A X))) at h
  rw [hv] at h
  exact h

/-- 元のnative fiber射の単位の辺の類は、元のnative対象の恒等射。 -/
lemma strictBETotJointSourceNativeTwistedFiberMap_unit_arrow (X : (operad A).Algebra) :
    Arrow.mk (HomotopyCategory.homMk (twistedArrowVertexEdge
      (((strictBETotJointSourceNativeTwistedFiberMap A (strictBETotJointUnitIndex A X)).app
        (Opposite.op ⦋0⦌) (nerveVertex (strictBETotJointSourceNativeUnitFiberElement A X))).val))) =
      Arrow.mk (𝟙 (HomotopyCategory.mk ((strictBETotModelSource A).app
        (Opposite.op ⦋0⦌) (nerveVertex (modelRelativeObject (operad A).Algebra X))))) := by
  have h := congrArg (fun v : (TwistedArrow (CAlg_R A)) _⦋0⦌ =>
    Arrow.mk (HomotopyCategory.homMk (twistedArrowVertexEdge v))) (strictBETotJointSourceNativeTwistedFiberMap_unit_value A X)
  exact h.trans (strictBETotJointSourceCorrectedPairing_unit_arrow A X)

end SerrePositivity.EInfinity.BarrattEccles

end
